#!/usr/bin/env bash
set -euo pipefail

PYODIDE_VERSION="${PYODIDE_VERSION:-0.27.0}"
PYODIDE_BASE_URL="${PYODIDE_BASE_URL:-https://cdn.jsdelivr.net/pyodide/v${PYODIDE_VERSION}/full}"
PYODIDE_DEST_DIR="${PYODIDE_DEST_DIR:-static/pyodide}"

REQUIRED_FILES=(
  "pyodide.js"
  "pyodide.mjs"
  "pyodide.asm.js"
  "pyodide.asm.wasm"
  "python_stdlib.zip"
  "pyodide-lock.json"
  "package.json"
)

OPTIONAL_FILES=(
  "repodata.json"
  "pyodide.asm.data"
)

echo "Syncing Pyodide ${PYODIDE_VERSION} into ${PYODIDE_DEST_DIR}"
mkdir -p "${PYODIDE_DEST_DIR}"

download_file() {
  local rel="$1"
  local url="${PYODIDE_BASE_URL}/${rel}"
  local dst="${PYODIDE_DEST_DIR}/${rel}"
  echo "  - ${rel}"
  curl -fL --retry 3 --retry-delay 1 --retry-connrefused "${url}" -o "${dst}"
}

for rel in "${REQUIRED_FILES[@]}"; do
  download_file "${rel}"
done

for rel in "${OPTIONAL_FILES[@]}"; do
  if curl -fsI "${PYODIDE_BASE_URL}/${rel}" >/dev/null; then
    download_file "${rel}"
  else
    echo "  - ${rel} (missing upstream, skipping)"
  fi
done

node - "${PYODIDE_DEST_DIR}" <<'NODE'
const fs = require('fs');
const path = require('path');

const destDir = process.argv[2];
const entries = fs
  .readdirSync(destDir, { withFileTypes: true })
  .filter((entry) => entry.isFile())
  .map((entry) => entry.name)
  .filter((name) => name !== 'pyodide-manifest.json')
  .sort();

const manifest = {
  basePath: './',
  files: entries
};

fs.writeFileSync(
  path.join(destDir, 'pyodide-manifest.json'),
  JSON.stringify(manifest, null, 2) + '\n',
  'utf8'
);
NODE

echo "Done. Wrote ${PYODIDE_DEST_DIR}/pyodide-manifest.json"
