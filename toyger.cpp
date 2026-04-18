#include <Xm/Xm.h>
#include <Xm/Form.h>
#include <Xm/Label.h>
#include <Xm/TextF.h>
#include <Xm/PushB.h>
#include <Xm/MessageB.h>
#include <Xm/VendorS.h>
#include <Xm/Protocols.h>

#include <X11/Shell.h>
#include <X11/Xatom.h>
#include <X11/keysym.h>
#include <X11/Xutil.h>

#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <optional>
#include <string>
#include <utility>
#include <vector>

namespace {

constexpr Dimension kWindowWidth = 420;
constexpr Dimension kWindowHeight = 126;

struct AppState {
    XtAppContext app_context{};
    Widget toplevel{};
    Widget form{};
    Widget label{};
    Widget text{};
    Widget button{};
};

struct ParseResult {
    bool ok{false};
    std::vector<std::string> argv;
    std::string error;
};

struct LaunchPrep {
    bool ok{false};
    std::vector<std::string> exec_argv;
    std::string error;
};

static std::string to_lower(std::string s) {
    for (char &ch : s) {
        ch = static_cast<char>(std::tolower(static_cast<unsigned char>(ch)));
    }
    return s;
}

static bool starts_with(const std::string &s, const std::string &prefix) {
    return s.size() >= prefix.size() &&
           std::equal(prefix.begin(), prefix.end(), s.begin());
}

static std::string basename_of(const std::string &path) {
    if (path.empty()) {
        return {};
    }

    std::size_t end = path.size();
    while (end > 0 && path[end - 1] == '/') {
        --end;
    }
    if (end == 0) {
        return "/";
    }

    std::size_t pos = path.rfind('/', end - 1);
    if (pos == std::string::npos) {
        return path.substr(0, end);
    }
    return path.substr(pos + 1, end - pos - 1);
}

static bool set_cloexec(int fd) {
    int flags = fcntl(fd, F_GETFD);
    if (flags < 0) {
        return false;
    }
    return fcntl(fd, F_SETFD, flags | FD_CLOEXEC) == 0;
}

static std::string errno_message(const std::string &prefix, int err) {
    return prefix + ": " + std::strerror(err);
}

static bool is_executable_file(const std::string &path) {
    struct stat st {};
    if (stat(path.c_str(), &st) != 0) {
        return false;
    }
    if (!S_ISREG(st.st_mode)) {
        return false;
    }
    return access(path.c_str(), X_OK) == 0;
}

static std::string normalize_path(const std::string &path) {
    char buf[PATH_MAX];
    if (realpath(path.c_str(), buf) != nullptr) {
        return std::string(buf);
    }
    return path;
}

static std::optional<std::string> resolve_executable(const std::string &command) {
    if (command.empty()) {
        return std::nullopt;
    }

    if (command.find('/') != std::string::npos) {
        if (is_executable_file(command)) {
            return normalize_path(command);
        }
        return std::nullopt;
    }

    const char *path_env = std::getenv("PATH");
    std::string path = path_env ? path_env : "/bin:/usr/bin:/usr/local/bin:/usr/X11R6/bin";

    std::size_t start = 0;
    while (start <= path.size()) {
        std::size_t end = path.find(':', start);
        std::string dir = (end == std::string::npos)
            ? path.substr(start)
            : path.substr(start, end - start);

        if (dir.empty()) {
            dir = ".";
        }

        std::string candidate = dir + "/" + command;
        if (is_executable_file(candidate)) {
            return normalize_path(candidate);
        }

        if (end == std::string::npos) {
            break;
        }
        start = end + 1;
    }

    return std::nullopt;
}

static bool read_file(const std::string &path, std::vector<unsigned char> &out) {
    std::ifstream in(path, std::ios::binary);
    if (!in) {
        return false;
    }

    in.seekg(0, std::ios::end);
    std::streamoff size = in.tellg();
    if (size < 0) {
        return false;
    }

    in.seekg(0, std::ios::beg);
    out.resize(static_cast<std::size_t>(size));

    if (size == 0) {
        return true;
    }

    in.read(reinterpret_cast<char *>(out.data()), size);
    return static_cast<std::size_t>(in.gcount()) == out.size();
}

static bool read_prefix_text(const std::string &path, std::string &out, std::size_t max_bytes) {
    std::ifstream in(path, std::ios::binary);
    if (!in) {
        return false;
    }

    std::vector<char> buf(max_bytes);
    in.read(buf.data(), static_cast<std::streamsize>(buf.size()));
    std::streamsize got = in.gcount();
    if (got <= 0) {
        out.clear();
        return true;
    }

    out.assign(buf.data(), static_cast<std::size_t>(got));
    return true;
}

static ParseResult parse_command_line(const std::string &input) {
    ParseResult result;
    std::vector<std::string> argv;
    std::string current;

    enum class QuoteMode {
        Plain,
        Single,
        Double
    };

    QuoteMode quote = QuoteMode::Plain;
    bool escaping = false;
    bool token_started = false;

    auto flush_token = [&]() {
        if (token_started) {
            argv.push_back(current);
            current.clear();
            token_started = false;
        }
    };

    auto shell_feature_error = [&]() -> ParseResult {
        ParseResult pr;
        pr.ok = false;
        pr.error =
            "Shell operators are intentionally not supported. "
            "Use a direct command with arguments only; pipes, ';', '&', redirection, "
            "variable expansion, and command substitution are rejected.";
        return pr;
    };

    for (char raw_ch : input) {
        unsigned char uch = static_cast<unsigned char>(raw_ch);
        char ch = static_cast<char>(uch);

        if (quote == QuoteMode::Plain) {
            if (escaping) {
                token_started = true;
                current.push_back(ch);
                escaping = false;
                continue;
            }

            if (ch == '\\') {
                token_started = true;
                escaping = true;
                continue;
            }

            if (std::isspace(uch)) {
                flush_token();
                continue;
            }

            if (ch == '\'') {
                token_started = true;
                quote = QuoteMode::Single;
                continue;
            }

            if (ch == '"') {
                token_started = true;
                quote = QuoteMode::Double;
                continue;
            }

            if (ch == '|' || ch == '&' || ch == ';' || ch == '<' || ch == '>' ||
                ch == '`' || ch == '$') {
                return shell_feature_error();
            }

            token_started = true;
            current.push_back(ch);
            continue;
        }

        if (quote == QuoteMode::Single) {
            if (ch == '\'') {
                quote = QuoteMode::Plain;
            } else {
                current.push_back(ch);
            }
            continue;
        }

        if (escaping) {
            if (ch == '"' || ch == '\\') {
                current.push_back(ch);
            } else {
                current.push_back('\\');
                current.push_back(ch);
            }
            escaping = false;
            continue;
        }

        if (ch == '\\') {
            escaping = true;
            continue;
        }

        if (ch == '"') {
            quote = QuoteMode::Plain;
            continue;
        }

        current.push_back(ch);
    }

    if (escaping) {
        current.push_back('\\');
    }

    if (quote != QuoteMode::Plain) {
        result.ok = false;
        result.error = "Unterminated quote in command line.";
        return result;
    }

    flush_token();

    if (argv.empty()) {
        result.ok = false;
        result.error = "Please enter a command.";
        return result;
    }

    result.ok = true;
    result.argv = std::move(argv);
    return result;
}

template <typename Addr>
static bool vaddr_to_offset(const std::vector<unsigned char> &bytes,
                            Addr vaddr,
                            const void *phdr_base,
                            std::size_t phnum,
                            std::size_t phentsize,
                            std::size_t &offset_out) {
    for (std::size_t i = 0; i < phnum; ++i) {
        const unsigned char *ptr =
            static_cast<const unsigned char *>(phdr_base) + (i * phentsize);

        if (phentsize == sizeof(Elf64_Phdr)) {
            const auto *ph = reinterpret_cast<const Elf64_Phdr *>(ptr);
            if (ph->p_filesz == 0) {
                continue;
            }
            if (vaddr >= ph->p_vaddr && vaddr < ph->p_vaddr + ph->p_memsz) {
                std::uint64_t delta = static_cast<std::uint64_t>(vaddr - ph->p_vaddr);
                if (delta >= ph->p_filesz) {
                    return false;
                }
                std::uint64_t off = ph->p_offset + delta;
                if (off >= bytes.size()) {
                    return false;
                }
                offset_out = static_cast<std::size_t>(off);
                return true;
            }
        } else if (phentsize == sizeof(Elf32_Phdr)) {
            const auto *ph = reinterpret_cast<const Elf32_Phdr *>(ptr);
            if (ph->p_filesz == 0) {
                continue;
            }
            if (vaddr >= ph->p_vaddr && vaddr < ph->p_vaddr + ph->p_memsz) {
                std::uint32_t delta = static_cast<std::uint32_t>(vaddr - ph->p_vaddr);
                if (delta >= ph->p_filesz) {
                    return false;
                }
                std::uint32_t off = ph->p_offset + delta;
                if (off >= bytes.size()) {
                    return false;
                }
                offset_out = static_cast<std::size_t>(off);
                return true;
            }
        }
    }

    return false;
}

static bool needed_library_name_looks_gui(const std::string &name) {
    static const std::vector<std::string> gui_libs = {
        "libx11", "libxt", "libxm", "libxaw", "libxmu",
        "libxext", "libxrender", "libxrandr", "libxi",
        "libxcursor", "libxinerama", "libxfixes",
        "libgtk", "libgdk", "libqt", "libwx", "libsdl",
        "libfltk", "libglfw", "libtk", "libfox",
        "libwayland-client", "libwayland-egl",
        "libwayland-cursor", "libxkbcommon"
    };

    std::string lower = to_lower(name);
    for (const auto &token : gui_libs) {
        if (lower.find(token) != std::string::npos) {
            return true;
        }
    }
    return false;
}

template <typename Ehdr, typename Phdr, typename Dyn, typename Addr>
static bool elf_dynamic_libraries_look_gui_t(const std::vector<unsigned char> &bytes) {
    if (bytes.size() < sizeof(Ehdr)) {
        return false;
    }

    const auto *eh = reinterpret_cast<const Ehdr *>(bytes.data());
    if (eh->e_phoff == 0 || eh->e_phnum == 0) {
        return false;
    }

    if (eh->e_phoff + (static_cast<std::size_t>(eh->e_phnum) * sizeof(Phdr)) > bytes.size()) {
        return false;
    }

    const auto *phdrs = reinterpret_cast<const Phdr *>(bytes.data() + eh->e_phoff);

    const Dyn *dyn = nullptr;
    std::size_t dyn_count = 0;

    for (std::size_t i = 0; i < eh->e_phnum; ++i) {
        if (phdrs[i].p_type == PT_DYNAMIC) {
            if (phdrs[i].p_offset + phdrs[i].p_filesz > bytes.size()) {
                return false;
            }
            dyn = reinterpret_cast<const Dyn *>(bytes.data() + phdrs[i].p_offset);
            dyn_count = static_cast<std::size_t>(phdrs[i].p_filesz / sizeof(Dyn));
            break;
        }
    }

    if (dyn == nullptr || dyn_count == 0) {
        return false;
    }

    Addr strtab_vaddr = 0;
    std::size_t strsz = 0;
    std::vector<std::size_t> needed_offsets;

    for (std::size_t i = 0; i < dyn_count; ++i) {
        if (dyn[i].d_tag == DT_NULL) {
            break;
        }

        if (dyn[i].d_tag == DT_STRTAB) {
            strtab_vaddr = static_cast<Addr>(dyn[i].d_un.d_ptr);
        } else if (dyn[i].d_tag == DT_STRSZ) {
            strsz = static_cast<std::size_t>(dyn[i].d_un.d_val);
        } else if (dyn[i].d_tag == DT_NEEDED) {
            needed_offsets.push_back(static_cast<std::size_t>(dyn[i].d_un.d_val));
        }
    }

    if (strtab_vaddr == 0 || strsz == 0 || needed_offsets.empty()) {
        return false;
    }

    std::size_t strtab_off = 0;
    if (!vaddr_to_offset<Addr>(bytes, strtab_vaddr, phdrs, eh->e_phnum, sizeof(Phdr), strtab_off)) {
        return false;
    }

    if (strtab_off >= bytes.size()) {
        return false;
    }

    const std::size_t max_strsz = bytes.size() - strtab_off;
    if (strsz > max_strsz) {
        strsz = max_strsz;
    }

    const char *strtab = reinterpret_cast<const char *>(bytes.data() + strtab_off);

    for (std::size_t off : needed_offsets) {
        if (off >= strsz) {
            continue;
        }

        std::string name(strtab + off);
        if (needed_library_name_looks_gui(name)) {
            return true;
        }
    }

    return false;
}

static bool raw_binary_contains_gui_symbols(const std::vector<unsigned char> &bytes) {
    static const std::vector<std::string> symbols = {
        "XOpenDisplay",
        "XCreateWindow",
        "XMapWindow",
        "XMapRaised",
        "XInternAtom",
        "XGetVisualInfo",
        "XSetWMProtocols",
        "XtAppInitialize",
        "XmCreate",
        "gtk_init",
        "gtk_application_new",
        "gtk_window_new",
        "QApplication",
        "QGuiApplication",
        "QWidget",
        "SDL_Init",
        "SDL_CreateWindow",
        "glfwInit",
        "glXChooseVisual",
        "glXCreateContext",
        "eglInitialize",
        "eglCreateWindowSurface",
        "wl_display_connect",
        "wl_compositor_create_surface",
        "Tk_Init"
    };

    for (const auto &sym : symbols) {
        auto it = std::search(bytes.begin(), bytes.end(), sym.begin(), sym.end());
        if (it != bytes.end()) {
            return true;
        }
    }

    return false;
}

static bool elf_looks_gui(const std::string &path) {
    std::vector<unsigned char> bytes;
    if (!read_file(path, bytes)) {
        return false;
    }

    if (bytes.size() < EI_NIDENT) {
        return false;
    }

    if (bytes[0] != ELFMAG0 || bytes[1] != ELFMAG1 ||
        bytes[2] != ELFMAG2 || bytes[3] != ELFMAG3) {
        return false;
    }

    bool gui_by_needed = false;

    if (bytes[EI_CLASS] == ELFCLASS64) {
        gui_by_needed = elf_dynamic_libraries_look_gui_t<Elf64_Ehdr, Elf64_Phdr, Elf64_Dyn, Elf64_Addr>(bytes);
    } else if (bytes[EI_CLASS] == ELFCLASS32) {
        gui_by_needed = elf_dynamic_libraries_look_gui_t<Elf32_Ehdr, Elf32_Phdr, Elf32_Dyn, Elf32_Addr>(bytes);
    }

    if (gui_by_needed) {
        return true;
    }

    return raw_binary_contains_gui_symbols(bytes);
}

static std::optional<std::vector<std::string>> read_shebang_tokens(const std::string &path) {
    std::string prefix;
    if (!read_prefix_text(path, prefix, 4096)) {
        return std::nullopt;
    }

    if (!starts_with(prefix, "#!")) {
        return std::nullopt;
    }

    std::size_t line_end = prefix.find('\n');
    std::string line = prefix.substr(2, line_end == std::string::npos ? std::string::npos : line_end - 2);

    std::vector<std::string> tokens;
    std::string current;
    for (char ch : line) {
        if (std::isspace(static_cast<unsigned char>(ch))) {
            if (!current.empty()) {
                tokens.push_back(current);
                current.clear();
            }
        } else {
            current.push_back(ch);
        }
    }
    if (!current.empty()) {
        tokens.push_back(current);
    }

    if (tokens.empty()) {
        return std::nullopt;
    }

    return tokens;
}

static bool is_known_gui_interpreter(const std::vector<std::string> &tokens) {
    if (tokens.empty()) {
        return false;
    }

    std::string interp = basename_of(tokens[0]);

    if (interp == "env") {
        for (std::size_t i = 1; i < tokens.size(); ++i) {
            if (!tokens[i].empty() && tokens[i][0] != '-') {
                interp = basename_of(tokens[i]);
                break;
            }
        }
    }

    interp = to_lower(interp);

    return interp == "wish" ||
           interp == "wish8.6" ||
           interp == "wish8.5" ||
           interp == "expectk";
}

static std::string trim_ascii(const std::string &s) {
    std::size_t start = 0;
    while (start < s.size() &&
           std::isspace(static_cast<unsigned char>(s[start]))) {
        ++start;
    }

    std::size_t end = s.size();
    while (end > start &&
           std::isspace(static_cast<unsigned char>(s[end - 1]))) {
        --end;
    }

    return s.substr(start, end - start);
}

static bool is_shell_name_start(char ch) {
    unsigned char uch = static_cast<unsigned char>(ch);
    return std::isalpha(uch) || ch == '_';
}

static bool is_shell_name_char(char ch) {
    unsigned char uch = static_cast<unsigned char>(ch);
    return std::isalnum(uch) || ch == '_';
}

static std::optional<std::string> lookup_shell_variable(
    const std::vector<std::pair<std::string, std::string>> &vars,
    const std::string &name) {
    for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
        if (it->first == name) {
            return it->second;
        }
    }

    const char *env = std::getenv(name.c_str());
    if (env != nullptr) {
        return std::string(env);
    }

    return std::nullopt;
}

static bool append_expanded_shell_variable(
    const std::string &input,
    std::size_t &i,
    const std::vector<std::pair<std::string, std::string>> &vars,
    std::string &out) {
    if (input[i] != '$') {
        return false;
    }

    if (i + 1 >= input.size()) {
        out.push_back('$');
        return true;
    }

    std::size_t name_start = 0;
    std::size_t name_end = 0;

    if (input[i + 1] == '{') {
        name_start = i + 2;
        name_end = name_start;

        while (name_end < input.size() && input[name_end] != '}') {
            ++name_end;
        }

        if (name_end >= input.size() || name_end == name_start) {
            return false;
        }

        for (std::size_t p = name_start; p < name_end; ++p) {
            if ((p == name_start && !is_shell_name_start(input[p])) ||
                !is_shell_name_char(input[p])) {
                return false;
            }
        }

        i = name_end;
    } else {
        if (!is_shell_name_start(input[i + 1])) {
            out.push_back('$');
            return true;
        }

        name_start = i + 1;
        name_end = name_start + 1;

        while (name_end < input.size() &&
               is_shell_name_char(input[name_end])) {
            ++name_end;
        }

        i = name_end - 1;
    }

    const std::string name = input.substr(name_start, name_end - name_start);
    auto value = lookup_shell_variable(vars, name);
    if (value.has_value()) {
        out += *value;
    }

    return true;
}

static bool extract_first_shell_word_expanded(
    const std::string &text,
    const std::vector<std::pair<std::string, std::string>> &vars,
    std::string &out,
    bool &had_word) {
    out.clear();
    had_word = false;

    enum class QuoteMode {
        Plain,
        Single,
        Double
    };

    QuoteMode quote = QuoteMode::Plain;
    bool escaping = false;

    for (std::size_t i = 0; i < text.size(); ++i) {
        unsigned char uch = static_cast<unsigned char>(text[i]);
        char ch = static_cast<char>(uch);

        if (quote == QuoteMode::Plain) {
            if (escaping) {
                out.push_back(ch);
                had_word = true;
                escaping = false;
                continue;
            }

            if (ch == '\\') {
                escaping = true;
                had_word = true;
                continue;
            }

            if (std::isspace(uch)) {
                if (had_word) {
                    break;
                }
                continue;
            }

            if (ch == '\'') {
                had_word = true;
                quote = QuoteMode::Single;
                continue;
            }

            if (ch == '"') {
                had_word = true;
                quote = QuoteMode::Double;
                continue;
            }

            if (ch == '$') {
                had_word = true;
                if (!append_expanded_shell_variable(text, i, vars, out)) {
                    return false;
                }
                continue;
            }

            if (ch == '|' || ch == '&' || ch == ';' || ch == '<' || ch == '>') {
                return had_word;
            }

            had_word = true;
            out.push_back(ch);
            continue;
        }

        if (quote == QuoteMode::Single) {
            if (ch == '\'') {
                quote = QuoteMode::Plain;
            } else {
                out.push_back(ch);
            }
            continue;
        }

        if (escaping) {
            if (ch == '"' || ch == '\\' || ch == '$') {
                out.push_back(ch);
            } else {
                out.push_back('\\');
                out.push_back(ch);
            }
            escaping = false;
            continue;
        }

        if (ch == '\\') {
            escaping = true;
            continue;
        }

        if (ch == '"') {
            quote = QuoteMode::Plain;
            continue;
        }

        if (ch == '$') {
            if (!append_expanded_shell_variable(text, i, vars, out)) {
                return false;
            }
            continue;
        }

        out.push_back(ch);
    }

    if (escaping) {
        out.push_back('\\');
    }

    return quote == QuoteMode::Plain;
}

static bool parse_simple_shell_assignment(
    const std::string &line,
    const std::vector<std::pair<std::string, std::string>> &vars,
    std::string &name_out,
    std::string &value_out) {
    const std::string trimmed = trim_ascii(line);
    if (trimmed.empty() || trimmed[0] == '#') {
        return false;
    }

    if (!is_shell_name_start(trimmed[0])) {
        return false;
    }

    std::size_t pos = 1;
    while (pos < trimmed.size() && is_shell_name_char(trimmed[pos])) {
        ++pos;
    }

    if (pos >= trimmed.size() || trimmed[pos] != '=') {
        return false;
    }

    name_out = trimmed.substr(0, pos);
    value_out.clear();

    const std::string value_expr = trimmed.substr(pos + 1);
    if (value_expr.empty()) {
        return true;
    }

    bool had_word = false;
    if (!extract_first_shell_word_expanded(value_expr, vars, value_out, had_word)) {
        return false;
    }

    return had_word || value_expr.empty();
}

static bool is_shell_interpreter(const std::vector<std::string> &tokens) {
    if (tokens.empty()) {
        return false;
    }

    std::string interp = basename_of(tokens[0]);

    if (interp == "env") {
        for (std::size_t i = 1; i < tokens.size(); ++i) {
            if (!tokens[i].empty() && tokens[i][0] != '-') {
                interp = basename_of(tokens[i]);
                break;
            }
        }
    }

    interp = to_lower(interp);

    return interp == "sh"   ||
           interp == "ksh"  ||
           interp == "oksh" ||
           interp == "mksh" ||
           interp == "bash" ||
           interp == "zsh"  ||
           interp == "dash" ||
           interp == "ash"  ||
           interp == "csh"  ||
           interp == "tcsh";
}

static std::optional<std::string> resolve_shell_wrapper_exec_target(const std::string &path) {
    auto shebang = read_shebang_tokens(path);
    if (!shebang.has_value() || !is_shell_interpreter(*shebang)) {
        return std::nullopt;
    }

    std::string prefix;
    if (!read_prefix_text(path, prefix, 32768)) {
        return std::nullopt;
    }

    std::vector<std::pair<std::string, std::string>> vars;

    std::size_t line_start = 0;
    while (line_start <= prefix.size()) {
        std::size_t line_end = prefix.find('\n', line_start);
        std::string line = prefix.substr(
            line_start,
            line_end == std::string::npos ? std::string::npos : line_end - line_start
        );

        const std::string trimmed = trim_ascii(line);
        if (!trimmed.empty() && trimmed[0] != '#') {
            std::string name;
            std::string value;

            if (parse_simple_shell_assignment(trimmed, vars, name, value)) {
                vars.emplace_back(name, value);
            } else if (starts_with(trimmed, "exec") &&
                       trimmed.size() > 4 &&
                       std::isspace(static_cast<unsigned char>(trimmed[4]))) {
                std::string target;
                bool had_word = false;

                if (!extract_first_shell_word_expanded(trimmed.substr(4), vars, target, had_word) ||
                    !had_word || target.empty()) {
                    return std::nullopt;
                }

                return resolve_executable(target);
            }
        }

        if (line_end == std::string::npos) {
            break;
        }
        line_start = line_end + 1;
    }

    return std::nullopt;
}

static bool script_text_looks_gui(const std::string &path) {
    std::string prefix;
    if (!read_prefix_text(path, prefix, 16384)) {
        return false;
    }

    std::string lower = to_lower(prefix);

    static const std::vector<std::string> markers = {
        "tkinter",
        "pyqt",
        "pyside",
        "gi.repository.gtk",
        "qtwidgets",
        "gtk.application",
        "import gtk",
        "wx.app",
        "wxpython",
        "fltk",
        "glfw",
        "sdl",
        "wish",
        "zenity",
        "yad"
    };

    for (const auto &m : markers) {
        if (lower.find(m) != std::string::npos) {
            return true;
        }
    }

    return false;
}

static bool command_looks_gui_impl(const std::string &resolved_path, int depth) {
    if (depth > 4) {
        return false;
    }

    if (elf_looks_gui(resolved_path)) {
        return true;
    }

    auto shebang = read_shebang_tokens(resolved_path);
    if (!shebang) {
        return false;
    }

    if (is_known_gui_interpreter(*shebang)) {
        return true;
    }

    if (script_text_looks_gui(resolved_path)) {
        return true;
    }

    auto wrapped_target = resolve_shell_wrapper_exec_target(resolved_path);
    if (wrapped_target && *wrapped_target != resolved_path) {
        return command_looks_gui_impl(*wrapped_target, depth + 1);
    }

    return false;
}

static bool command_looks_gui(const std::string &resolved_path) {
    return command_looks_gui_impl(resolved_path, 0);
}

static LaunchPrep prepare_launch(const std::string &raw_input) {
    LaunchPrep prep;

    ParseResult parsed = parse_command_line(raw_input);
    if (!parsed.ok) {
        prep.error = parsed.error;
        return prep;
    }

    auto resolved = resolve_executable(parsed.argv[0]);
    if (!resolved) {
        prep.error = "Command not found or not executable: " + parsed.argv[0];
        return prep;
    }

    const bool is_gui = command_looks_gui(*resolved);

    if (is_gui) {
        prep.exec_argv = parsed.argv;
        prep.exec_argv[0] = *resolved;
        prep.ok = true;
        return prep;
    }

    auto xterm = resolve_executable("xterm");
    if (!xterm) {
        prep.error =
            "The command was classified as terminal/CLI, but xterm was not found in PATH.";
        return prep;
    }

    prep.exec_argv.clear();
    prep.exec_argv.push_back(*xterm);
    prep.exec_argv.push_back("-e");
    prep.exec_argv.push_back(*resolved);
    for (std::size_t i = 1; i < parsed.argv.size(); ++i) {
        prep.exec_argv.push_back(parsed.argv[i]);
    }

    prep.ok = true;
    return prep;
}

static std::vector<char *> make_exec_argv(std::vector<std::string> &args) {
    std::vector<char *> out;
    out.reserve(args.size() + 1);
    for (auto &s : args) {
        out.push_back(const_cast<char *>(s.c_str()));
    }
    out.push_back(nullptr);
    return out;
}

static bool write_errno_to_pipe(int fd, int err) {
    const unsigned char *p = reinterpret_cast<const unsigned char *>(&err);
    std::size_t left = sizeof(err);

    while (left > 0) {
        ssize_t n = write(fd, p, left);
        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }
            return false;
        }
        p += n;
        left -= static_cast<std::size_t>(n);
    }

    return true;
}

static std::optional<int> read_child_exec_errno(int fd, int &read_err) {
    int child_errno = 0;
    unsigned char *p = reinterpret_cast<unsigned char *>(&child_errno);
    std::size_t got = 0;

    for (;;) {
        ssize_t n = read(fd, p + got, sizeof(child_errno) - got);
        if (n == 0) {
            if (got == 0) {
                return std::nullopt;
            }
            read_err = EIO;
            return EIO;
        }
        if (n < 0) {
            if (errno == EINTR) {
                continue;
            }
            read_err = errno;
            return errno;
        }

        got += static_cast<std::size_t>(n);
        if (got == sizeof(child_errno)) {
            return child_errno;
        }
    }
}

static bool spawn_detached(std::vector<std::string> exec_argv, std::string &error) {
    int pipefd[2] = {-1, -1};
    if (pipe(pipefd) != 0) {
        error = errno_message("pipe failed", errno);
        return false;
    }

    if (!set_cloexec(pipefd[0]) || !set_cloexec(pipefd[1])) {
        int saved = errno;
        close(pipefd[0]);
        close(pipefd[1]);
        error = errno_message("fcntl(FD_CLOEXEC) failed", saved);
        return false;
    }

    pid_t pid = fork();
    if (pid < 0) {
        int saved = errno;
        close(pipefd[0]);
        close(pipefd[1]);
        error = errno_message("fork failed", saved);
        return false;
    }

    if (pid == 0) {
        close(pipefd[0]);

        if (setsid() < 0) {
            write_errno_to_pipe(pipefd[1], errno);
            _exit(127);
        }

        pid_t pid2 = fork();
        if (pid2 < 0) {
            write_errno_to_pipe(pipefd[1], errno);
            _exit(127);
        }

        if (pid2 > 0) {
            _exit(0);
        }

        signal(SIGHUP, SIG_IGN);
        signal(SIGPIPE, SIG_DFL);

        if (pipefd[1] != 3) {
            if (dup2(pipefd[1], 3) < 0) {
                write_errno_to_pipe(pipefd[1], errno);
                _exit(127);
            }
            close(pipefd[1]);
            pipefd[1] = 3;
        }

        if (!set_cloexec(pipefd[1])) {
            write_errno_to_pipe(pipefd[1], errno);
            _exit(127);
        }

        int devnull = open("/dev/null", O_RDWR);
        if (devnull >= 0) {
            (void)dup2(devnull, STDIN_FILENO);
            (void)dup2(devnull, STDOUT_FILENO);
            (void)dup2(devnull, STDERR_FILENO);
            if (devnull > STDERR_FILENO) {
                close(devnull);
            }
        }

        closefrom(4);

        auto argv = make_exec_argv(exec_argv);
        execv(exec_argv[0].c_str(), argv.data());

        write_errno_to_pipe(pipefd[1], errno);
        _exit(127);
    }

    close(pipefd[1]);

    int read_err = 0;
    std::optional<int> child_exec_errno = read_child_exec_errno(pipefd[0], read_err);
    close(pipefd[0]);

    int status = 0;
    while (waitpid(pid, &status, 0) < 0) {
        if (errno == EINTR) {
            continue;
        }
        break;
    }

    if (!child_exec_errno.has_value()) {
        return true;
    }

    int err = *child_exec_errno;
    if (err == EIO && read_err != 0) {
        err = read_err;
    }

    error = errno_message("launch failed", err);
    return false;
}

static XmString xm_string(const std::string &s) {
    return XmStringCreateLocalized(const_cast<char *>(s.c_str()));
}

static void show_error_dialog(AppState *app, const std::string &message) {
    Widget dialog = XmCreateErrorDialog(app->toplevel, const_cast<char *>("toyger_error"), nullptr, 0);

    XtUnmanageChild(XmMessageBoxGetChild(dialog, XmDIALOG_CANCEL_BUTTON));
    XtUnmanageChild(XmMessageBoxGetChild(dialog, XmDIALOG_HELP_BUTTON));

    XmString msg = xm_string(message);
    XmString title = xm_string("toyger error");

    XtVaSetValues(
        dialog,
        XmNmessageString, msg,
        XmNdialogTitle, title,
        nullptr
    );

    XmStringFree(msg);
    XmStringFree(title);

    XtManageChild(dialog);
}

static void close_launcher() {
    std::exit(0);
}

static void request_above_and_dialog_type(Widget shell) {
    Display *dpy = XtDisplay(shell);
    Window win = XtWindow(shell);
    Window root = DefaultRootWindow(dpy);

    Atom net_wm_state = XInternAtom(dpy, "_NET_WM_STATE", False);
    Atom net_wm_state_above = XInternAtom(dpy, "_NET_WM_STATE_ABOVE", False);
    Atom net_wm_window_type = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE", False);
    Atom net_wm_window_type_dialog = XInternAtom(dpy, "_NET_WM_WINDOW_TYPE_DIALOG", False);

    if (net_wm_window_type != None && net_wm_window_type_dialog != None) {
        Atom value = net_wm_window_type_dialog;
        XChangeProperty(
            dpy,
            win,
            net_wm_window_type,
            XA_ATOM,
            32,
            PropModeReplace,
            reinterpret_cast<unsigned char *>(&value),
            1
        );
    }

    if (net_wm_state != None && net_wm_state_above != None) {
        Atom value = net_wm_state_above;
        XChangeProperty(
            dpy,
            win,
            net_wm_state,
            XA_ATOM,
            32,
            PropModeReplace,
            reinterpret_cast<unsigned char *>(&value),
            1
        );

        XEvent ev {};
        ev.xclient.type = ClientMessage;
        ev.xclient.window = win;
        ev.xclient.message_type = net_wm_state;
        ev.xclient.format = 32;
        ev.xclient.data.l[0] = 1;
        ev.xclient.data.l[1] = net_wm_state_above;
        ev.xclient.data.l[2] = 0;
        ev.xclient.data.l[3] = 1;
        ev.xclient.data.l[4] = 0;

        XSendEvent(
            dpy,
            root,
            False,
            SubstructureRedirectMask | SubstructureNotifyMask,
            &ev
        );
    }

    XRaiseWindow(dpy, win);
    XFlush(dpy);
}

static void set_fixed_size(Widget shell) {
    Display *dpy = XtDisplay(shell);
    Window win = XtWindow(shell);

    Dimension width = 0;
    Dimension height = 0;
    XtVaGetValues(shell, XmNwidth, &width, XmNheight, &height, nullptr);

    XSizeHints hints {};
    hints.flags = PMinSize | PMaxSize;
    hints.min_width = static_cast<int>(width);
    hints.max_width = static_cast<int>(width);
    hints.min_height = static_cast<int>(height);
    hints.max_height = static_cast<int>(height);
    XSetWMNormalHints(dpy, win, &hints);
}

static void execute_from_ui(AppState *app) {
    char *raw = XmTextFieldGetString(app->text);
    std::string input = raw ? raw : "";
    if (raw != nullptr) {
        XtFree(raw);
    }

    LaunchPrep prep = prepare_launch(input);
    if (!prep.ok) {
        show_error_dialog(app, prep.error);
        return;
    }

    std::string launch_error;
    if (!spawn_detached(std::move(prep.exec_argv), launch_error)) {
        show_error_dialog(app, launch_error);
        return;
    }

    close_launcher();
}

extern "C" void activate_callback(Widget, XtPointer client_data, XtPointer) {
    auto *app = static_cast<AppState *>(client_data);
    execute_from_ui(app);
}

extern "C" void wm_delete_callback(Widget, XtPointer, XtPointer) {
    close_launcher();
}

extern "C" void escape_key_handler(Widget, XtPointer, XEvent *event, Boolean *) {
    if (event == nullptr || event->type != KeyPress) {
        return;
    }

    KeySym ks = XLookupKeysym(&event->xkey, 0);
    if (ks == XK_Escape) {
        close_launcher();
    }
}

} // namespace

int main(int argc, char **argv) {
    XtSetLanguageProc(nullptr, nullptr, nullptr);

    AppState app {};
    app.toplevel = XtVaAppInitialize(
        &app.app_context,
        const_cast<char *>("Toyger"),
        nullptr,
        0,
        &argc,
        argv,
        nullptr,
        XmNmwmDecorations, 0,
        XmNmwmFunctions, 0,
        XmNallowShellResize, False,
        XmNwidth, kWindowWidth,
        XmNheight, kWindowHeight,
        nullptr
    );

    Display *dpy = XtDisplay(app.toplevel);
    int screen = DefaultScreen(dpy);
    int sw = DisplayWidth(dpy, screen);
    int sh = DisplayHeight(dpy, screen);

    int pos_x = (sw - static_cast<int>(kWindowWidth)) / 2;
    int pos_y = (sh - static_cast<int>(kWindowHeight)) / 2;

    XtVaSetValues(
        app.toplevel,
        XmNx, pos_x,
        XmNy, pos_y,
        nullptr
    );

    app.form = XtVaCreateManagedWidget(
        "form",
        xmFormWidgetClass,
        app.toplevel,
        XmNmarginWidth, 0,
        XmNmarginHeight, 0,
        XmNfractionBase, 100,
        nullptr
    );

    XmString prompt = xm_string("Run something");
    app.label = XtVaCreateManagedWidget(
        "prompt",
        xmLabelWidgetClass,
        app.form,
        XmNlabelString, prompt,
        XmNalignment, XmALIGNMENT_BEGINNING,
        XmNtopAttachment, XmATTACH_FORM,
        XmNleftAttachment, XmATTACH_FORM,
        XmNrightAttachment, XmATTACH_FORM,
        XmNtopOffset, 14,
        XmNleftOffset, 14,
        XmNrightOffset, 14,
        nullptr
    );
    XmStringFree(prompt);

    app.text = XtVaCreateManagedWidget(
        "command",
        xmTextFieldWidgetClass,
        app.form,
        XmNcolumns, 44,
        XmNtopAttachment, XmATTACH_WIDGET,
        XmNtopWidget, app.label,
        XmNleftAttachment, XmATTACH_FORM,
        XmNrightAttachment, XmATTACH_FORM,
        XmNtopOffset, 8,
        XmNleftOffset, 14,
        XmNrightOffset, 14,
        nullptr
    );

    XmString button_label = xm_string("Execute");
    app.button = XtVaCreateManagedWidget(
        "execute",
        xmPushButtonWidgetClass,
        app.form,
        XmNlabelString, button_label,
        XmNtopAttachment, XmATTACH_WIDGET,
        XmNtopWidget, app.text,
        XmNrightAttachment, XmATTACH_FORM,
        XmNbottomAttachment, XmATTACH_FORM,
        XmNtopOffset, 10,
        XmNrightOffset, 14,
        XmNbottomOffset, 14,
        nullptr
    );
    XmStringFree(button_label);

    XtVaSetValues(app.form, XmNdefaultButton, app.button, nullptr);

    XtAddCallback(app.text, XmNactivateCallback, activate_callback, &app);
    XtAddCallback(app.button, XmNactivateCallback, activate_callback, &app);

    XtAddEventHandler(app.text, KeyPressMask, False, escape_key_handler, nullptr);
    XtAddEventHandler(app.button, KeyPressMask, False, escape_key_handler, nullptr);
    XtAddEventHandler(app.form, KeyPressMask, False, escape_key_handler, nullptr);

    Atom wm_delete = XmInternAtom(dpy, const_cast<char *>("WM_DELETE_WINDOW"), False);
    XmAddWMProtocolCallback(app.toplevel, wm_delete, wm_delete_callback, nullptr);

    XtRealizeWidget(app.toplevel);

    set_fixed_size(app.toplevel);
    request_above_and_dialog_type(app.toplevel);

    XMoveWindow(dpy, XtWindow(app.toplevel), pos_x, pos_y);
    XRaiseWindow(dpy, XtWindow(app.toplevel));
    XmProcessTraversal(app.text, XmTRAVERSE_CURRENT);
    XFlush(dpy);

    XtAppMainLoop(app.app_context);
    return 0;
}
