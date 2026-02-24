#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT_DIR/scripts/toolchain.lock.sh"

WITH_WASM=0
STRICT_NODE_VERSION="${STRICT_NODE_VERSION:-1}"
while (($#)); do
  case "$1" in
    --with-wasm)
      WITH_WASM=1
      shift
      ;;
    *)
      echo "Unknown argument: $1" >&2
      echo "Usage: $0 [--with-wasm]" >&2
      exit 1
      ;;
  esac
done

require_cmd() {
  local cmd="$1"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "Missing required command: $cmd" >&2
    exit 1
  fi
}

version_ge() {
  local current="$1"
  local minimum="$2"
  local i limit
  local current_part minimum_part
  local -a current_parts minimum_parts
  IFS='.' read -r -a current_parts <<< "$current"
  IFS='.' read -r -a minimum_parts <<< "$minimum"

  if ((${#current_parts[@]} > ${#minimum_parts[@]})); then
    limit=${#current_parts[@]}
  else
    limit=${#minimum_parts[@]}
  fi

  for ((i = 0; i < limit; i++)); do
    current_part="${current_parts[i]:-0}"
    minimum_part="${minimum_parts[i]:-0}"
    if ((10#$current_part > 10#$minimum_part)); then
      return 0
    fi
    if ((10#$current_part < 10#$minimum_part)); then
      return 1
    fi
  done
  return 0
}

require_cmd git
require_cmd node
require_cmd npm
require_cmd unzip

node_major="$(node -p 'process.versions.node.split(".")[0]')"
if [[ "$node_major" != "$NODE_MAJOR_VERSION_LOCKED" ]]; then
  if [[ "$STRICT_NODE_VERSION" == "1" ]]; then
    echo "Node major mismatch: expected $NODE_MAJOR_VERSION_LOCKED.x, got $(node -v)" >&2
    echo "Set STRICT_NODE_VERSION=0 to continue with a non-pinned Node for local experiments." >&2
    exit 1
  fi
  echo "Warning: Node major mismatch (expected $NODE_MAJOR_VERSION_LOCKED.x, got $(node -v))." >&2
fi

if [[ "$WITH_WASM" == "1" ]]; then
  require_cmd cmake
  require_cmd ninja
  require_cmd rsync
  require_cmd emcc
  require_cmd emcmake

  cmake_version="$(cmake --version | sed -n '1s/^cmake version //p')"
  if ! version_ge "$cmake_version" "3.24"; then
    echo "cmake >= 3.24 is required, got $cmake_version" >&2
    exit 1
  fi

  python_cmd=""
  if command -v python3 >/dev/null 2>&1; then
    python_version="$(python3 --version | awk '{print $2}')"
    if version_ge "$python_version" "3.10"; then
      python_cmd="python3"
    fi
  fi
  if [[ -z "$python_cmd" && -n "${EMSDK_PYTHON:-}" && -x "${EMSDK_PYTHON:-}" ]]; then
    python_version="$("$EMSDK_PYTHON" --version | awk '{print $2}')"
    if version_ge "$python_version" "3.10"; then
      python_cmd="$EMSDK_PYTHON"
    fi
  fi
  if [[ -z "$python_cmd" ]]; then
    echo "python >= 3.10 is required (python3 or EMSDK_PYTHON)." >&2
    exit 1
  fi

  ninja_version="$(ninja --version)"
  if ! version_ge "$ninja_version" "1.10"; then
    echo "ninja >= 1.10 is required, got $ninja_version" >&2
    exit 1
  fi

  emcc_version_line="$(emcc -v 2>&1 | sed -n '1p')"
  if [[ "$emcc_version_line" != *"$EMSDK_VERSION_LOCKED"* ]]; then
    echo "Emscripten version mismatch: expected $EMSDK_VERSION_LOCKED, got: $emcc_version_line" >&2
    echo "Tip: source your emsdk env before building wasm." >&2
    exit 1
  fi
fi

echo "Requirements check passed."
