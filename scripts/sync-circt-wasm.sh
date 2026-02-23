#!/usr/bin/env bash
set -euo pipefail

SRC_DIR="${1:-vendor/circt/build-wasm/bin}"
DST_DIR="${2:-public/circt}"

TOOLS=("circt-bmc" "circt-sim")
missing=()

for tool in "${TOOLS[@]}"; do
  if [ ! -f "$SRC_DIR/$tool.js" ]; then
    missing+=("$tool.js")
  fi
  if [ ! -f "$SRC_DIR/$tool.wasm" ]; then
    missing+=("$tool.wasm")
  fi
done

if [ "${#missing[@]}" -ne 0 ]; then
  echo "Missing CIRCT wasm artifacts in $SRC_DIR" >&2
  echo "Missing files: ${missing[*]}" >&2
  exit 1
fi

mkdir -p "$DST_DIR"
for tool in "${TOOLS[@]}"; do
  cp -f "$SRC_DIR/$tool.js" "$DST_DIR/$tool.js"
  cp -f "$SRC_DIR/$tool.wasm" "$DST_DIR/$tool.wasm"
done
cat >"$DST_DIR/package.json" <<'EOF'
{
  "type": "commonjs"
}
EOF

echo "Synced CIRCT wasm artifacts:"
for tool in "${TOOLS[@]}"; do
  ls -lh "$DST_DIR/$tool.js" "$DST_DIR/$tool.wasm"
done
