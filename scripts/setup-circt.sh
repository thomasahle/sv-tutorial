#!/usr/bin/env bash
set -euo pipefail

CIRCT_REPO="${CIRCT_REPO:-git@github.com:thomasnormal/circt.git}"
TARGET_DIR="${1:-vendor/circt}"

if [ -d "$TARGET_DIR/.git" ]; then
  echo "Updating existing CIRCT checkout in $TARGET_DIR"
  git -C "$TARGET_DIR" fetch --all --tags
  git -C "$TARGET_DIR" pull --ff-only
else
  echo "Cloning CIRCT fork from $CIRCT_REPO into $TARGET_DIR"
  git clone "$CIRCT_REPO" "$TARGET_DIR"
fi

cat <<'MSG'

CIRCT fork checkout is ready.

Next:
1. Build wasm artifacts from the fork checkout.
2. Copy generated runtime files to:
   public/circt/circt-verilog.js
   public/circt/circt-verilog.wasm
   public/circt/circt-bmc.js
   public/circt/circt-bmc.wasm
   public/circt/circt-sim.js
   public/circt/circt-sim.wasm
   (or provide a custom shim pair: circt.js + circt.wasm)
3. Optionally override URLs with:
   VITE_CIRCT_VERILOG_JS_URL / VITE_CIRCT_VERILOG_WASM_URL
   VITE_CIRCT_SIM_JS_URL / VITE_CIRCT_SIM_WASM_URL
   VITE_CIRCT_BMC_JS_URL / VITE_CIRCT_BMC_WASM_URL

MSG
