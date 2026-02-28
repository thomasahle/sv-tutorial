#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT_DIR/scripts/toolchain.lock.sh"

CIRCT_REPO="${CIRCT_REPO:-$CIRCT_REPO_LOCKED}"
CIRCT_REF="${CIRCT_REF:-$CIRCT_REF_LOCKED}"
CIRCT_LLVM_SUBMODULE_REF="${CIRCT_LLVM_SUBMODULE_REF:-$CIRCT_LLVM_SUBMODULE_REF_LOCKED}"
TARGET_DIR="${1:-vendor/circt}"
ALLOW_DIRTY="${ALLOW_DIRTY:-0}"

require_clean_worktree() {
  local repo_dir="$1"
  if [[ "$ALLOW_DIRTY" == "1" ]]; then
    return 0
  fi
  if [[ -n "$(git -C "$repo_dir" status --porcelain)" ]]; then
    echo "Refusing to update dirty checkout: $repo_dir" >&2
    echo "Set ALLOW_DIRTY=1 to override." >&2
    exit 1
  fi
}

if [ -d "$TARGET_DIR/.git" ]; then
  echo "Updating existing CIRCT checkout in $TARGET_DIR"
  require_clean_worktree "$TARGET_DIR"
  git -C "$TARGET_DIR" remote set-url origin "$CIRCT_REPO"
  git -C "$TARGET_DIR" fetch --tags origin
else
  echo "Cloning CIRCT fork from $CIRCT_REPO into $TARGET_DIR"
  git clone "$CIRCT_REPO" "$TARGET_DIR"
fi

git -C "$TARGET_DIR" fetch --tags origin "$CIRCT_REF"
git -C "$TARGET_DIR" checkout --detach "$CIRCT_REF"
git -C "$TARGET_DIR" submodule sync --recursive
git -C "$TARGET_DIR" submodule update --init --recursive --checkout

if [ -n "$CIRCT_LLVM_SUBMODULE_REF" ]; then
  actual_llvm_ref="$(git -C "$TARGET_DIR/llvm" rev-parse HEAD)"
  if [[ "$actual_llvm_ref" != "$CIRCT_LLVM_SUBMODULE_REF" ]]; then
    echo "LLVM submodule ref mismatch in $TARGET_DIR/llvm" >&2
    echo "Expected: $CIRCT_LLVM_SUBMODULE_REF" >&2
    echo "Actual:   $actual_llvm_ref" >&2
    exit 1
  fi
fi

cat <<MSG

CIRCT fork checkout is ready.
Pinned repo: $CIRCT_REPO
Pinned ref:  $CIRCT_REF
LLVM ref:    $CIRCT_LLVM_SUBMODULE_REF

Next:
1. Build wasm artifacts from the fork checkout.
   Standard tools (circt-verilog, circt-sim, circt-bmc):
     cmake ... -DCIRCT_SIM_WASM=ON -DCIRCT_BMC_WASM=ON
   VPI-capable sim for cocotb lessons (additional build target):
     cmake ... -DCIRCT_SIM_WASM_VPI=ON
2. Run npm run local-publish:circt (or publish:circt to also push to GitHub Release).
   (The script also patches browser-compatibility issues in circt-sim.js.)
3. Optionally override artifact URLs with VITE_* env vars in .env:
   VITE_CIRCT_VERILOG_JS_URL / VITE_CIRCT_VERILOG_WASM_URL
   VITE_CIRCT_SIM_JS_URL / VITE_CIRCT_SIM_WASM_URL
   VITE_CIRCT_BMC_JS_URL / VITE_CIRCT_BMC_WASM_URL
   VITE_CIRCT_SIM_VPI_JS_URL / VITE_CIRCT_SIM_VPI_WASM_URL

MSG
