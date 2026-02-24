#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT_DIR/scripts/toolchain.lock.sh"

CIRCT_DIR="${1:-vendor/circt}"
BUILD_DIR="${BUILD_DIR:-$CIRCT_DIR/build-wasm}"
JOBS="${CIRCT_WASM_JOBS:-4}"
CONFIGURE_TIMEOUT_MIN="${CIRCT_WASM_CONFIGURE_TIMEOUT_MIN:-30}"
BUILD_TIMEOUT_MIN="${CIRCT_WASM_BUILD_TIMEOUT_MIN:-120}"
MEMORY_LIMIT_KB="${CIRCT_WASM_MEMORY_LIMIT_KB:-0}"
SKIP_BUILD="${CIRCT_WASM_SKIP_BUILD:-0}"
TARGETS_RAW="${CIRCT_WASM_TARGETS:-circt-verilog circt-sim circt-bmc}"
CLEAN_BUILD="${CIRCT_WASM_CLEAN_BUILD:-0}"
AUTO_RETRY_CLEAN="${CIRCT_WASM_AUTO_RETRY_CLEAN:-1}"

if [[ ! "$JOBS" =~ ^[1-9][0-9]*$ ]]; then
  echo "CIRCT_WASM_JOBS must be a positive integer (got $JOBS)" >&2
  exit 1
fi

run_configure() {
  echo "Configuring wasm build in $BUILD_DIR"
  run_with_timeout "$CONFIGURE_TIMEOUT_MIN" \
    nice -n 10 env BUILD_DIR="$BUILD_DIR" \
    "$CIRCT_DIR/utils/configure_wasm_build.sh"
}

run_build() {
  echo "Building targets: ${targets[*]} (jobs=$JOBS)"
  run_with_timeout "$BUILD_TIMEOUT_MIN" \
    nice -n 10 ninja -C "$BUILD_DIR" -j"$JOBS" "${targets[@]}"
}

run_with_timeout() {
  local minutes="$1"
  shift
  if command -v timeout >/dev/null 2>&1; then
    timeout --preserve-status "${minutes}m" "$@"
    return
  fi
  if command -v gtimeout >/dev/null 2>&1; then
    gtimeout --preserve-status "${minutes}m" "$@"
    return
  fi
  echo "Warning: timeout/gtimeout not found; running without wall-clock guard." >&2
  "$@"
}

if [[ "$MEMORY_LIMIT_KB" != "0" ]]; then
  if ulimit -v "$MEMORY_LIMIT_KB" >/dev/null 2>&1; then
    echo "Applied virtual memory limit: ${MEMORY_LIMIT_KB} KB"
  else
    echo "Warning: unable to apply ulimit -v=$MEMORY_LIMIT_KB on this shell/platform." >&2
  fi
fi

STRICT_NODE_VERSION=0 "$ROOT_DIR/scripts/check-requirements.sh" --with-wasm

if [[ ! -d "$CIRCT_DIR" ]]; then
  echo "Missing CIRCT checkout: $CIRCT_DIR" >&2
  echo "Run scripts/setup-circt.sh first." >&2
  exit 1
fi

read -r -a targets <<< "$TARGETS_RAW"
if ((${#targets[@]} == 0)); then
  echo "CIRCT_WASM_TARGETS resolved to an empty target list." >&2
  exit 1
fi

if [[ "$CLEAN_BUILD" == "1" && -d "$BUILD_DIR" ]]; then
  echo "Cleaning build directory: $BUILD_DIR"
  cmake -E rm -rf "$BUILD_DIR"
fi

run_configure

if [[ "$SKIP_BUILD" == "1" ]]; then
  echo "Skipping ninja build because CIRCT_WASM_SKIP_BUILD=1"
  exit 0
fi

if ! run_build; then
  if [[ "$AUTO_RETRY_CLEAN" == "1" && "$CLEAN_BUILD" != "1" ]]; then
    echo "Initial build failed; retrying once from a clean build directory."
    cmake -E rm -rf "$BUILD_DIR"
    run_configure
    run_build
  else
    exit 1
  fi
fi

echo "Built CIRCT wasm artifacts in: $BUILD_DIR/bin"
ls -lh \
  "$BUILD_DIR/bin/circt-verilog.js" "$BUILD_DIR/bin/circt-verilog.wasm" \
  "$BUILD_DIR/bin/circt-sim.js" "$BUILD_DIR/bin/circt-sim.wasm" \
  "$BUILD_DIR/bin/circt-bmc.js" "$BUILD_DIR/bin/circt-bmc.wasm"
