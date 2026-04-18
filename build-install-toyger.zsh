#!/usr/bin/env zsh

set -euo pipefail

SCRIPT_NAME="${0:t}"
PROJECT_NAME="toyger"
SOURCE_FILE="toyger.cpp"
BUILD_OUTPUT="./toyger"
INSTALL_DIR="/usr/local/bin"
INSTALL_PATH="${INSTALL_DIR}/${PROJECT_NAME}"

CXX_BIN="${CXX:-c++}"
CXXFLAGS=(
  -std=c++20
  -O2
  -Wall
  -Wextra
  -Wno-register
  -pedantic
)
CPPFLAGS=(
  -I/usr/local/include
  -I/usr/X11R6/include
)
LDFLAGS_LOCAL=(
  -L/usr/local/lib
  -L/usr/X11R6/lib
  -lXm
  -lXt
  -lX11
)

log() {
  print -- "[${PROJECT_NAME}] $*"
}

fail() {
  print -u2 -- "[${PROJECT_NAME}] ERROR: $*"
  exit 1
}

warn_big_overwrite() {
  print
  print -- "============================================================"
  print -- "====================== WARNING ============================="
  print -- "============================================================"
  print -- "An existing installation of '${PROJECT_NAME}' was found."
  print -- "It will be overwritten now as requested."
  print -- "Target: ${INSTALL_PATH}"
  print -- "============================================================"
  print
}

need_cmd() {
  command -v "$1" >/dev/null 2>&1 || fail "Required command not found: $1"
}

run_privileged() {
  if [[ "${EUID}" -eq 0 ]]; then
    "$@"
    return
  fi

  if command -v doas >/dev/null 2>&1; then
    doas "$@"
    return
  fi

  fail "Root privileges are required to install into ${INSTALL_DIR}. Please run as root or install doas."
}

check_environment() {
  need_cmd "${CXX_BIN}"
  need_cmd install
  need_cmd chmod
  need_cmd mkdir

  [[ -f "${SOURCE_FILE}" ]] || fail "Source file not found in current directory: ${SOURCE_FILE}"
}

build_binary() {
  log "Building ${SOURCE_FILE} -> ${BUILD_OUTPUT}"
  "${CXX_BIN}" \
    "${CXXFLAGS[@]}" \
    "${SOURCE_FILE}" \
    -o "${BUILD_OUTPUT}" \
    "${CPPFLAGS[@]}" \
    "${LDFLAGS_LOCAL[@]}"

  [[ -f "${BUILD_OUTPUT}" ]] || fail "Build finished without producing ${BUILD_OUTPUT}"
  chmod 0755 "${BUILD_OUTPUT}" || fail "Could not chmod build output"
}

check_existing_installation() {
  if [[ -e "${INSTALL_PATH}" ]]; then
    warn_big_overwrite
    return
  fi

  local existing_cmd=""
  existing_cmd="$(command -v "${PROJECT_NAME}" 2>/dev/null || true)"
  if [[ -n "${existing_cmd}" && "${existing_cmd}" != "${INSTALL_PATH}" ]]; then
    print
    print -- "============================================================"
    print -- "====================== WARNING ============================="
    print -- "============================================================"
    print -- "Another '${PROJECT_NAME}' executable is already visible in PATH."
    print -- "Visible path: ${existing_cmd}"
    print -- "This script will install/overwrite only:"
    print -- "Target path: ${INSTALL_PATH}"
    print -- "============================================================"
    print
  fi
}

install_binary() {
  log "Ensuring install directory exists: ${INSTALL_DIR}"
  run_privileged mkdir -p "${INSTALL_DIR}"

  log "Installing ${PROJECT_NAME} to ${INSTALL_PATH}"
  run_privileged install -m 0755 "${BUILD_OUTPUT}" "${INSTALL_PATH}"

  log "Installation complete"
  log "Installed binary: ${INSTALL_PATH}"
}

main() {
  check_environment
  check_existing_installation
  build_binary
  install_binary
}

main "$@"
