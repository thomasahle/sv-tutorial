#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

cd "$ROOT_DIR"

scripts/check-requirements.sh
npm ci
scripts/setup-surfer.sh
scripts/setup-circt.sh
scripts/build-circt-wasm.sh
npm run sync:circt
npm run build

echo "Bootstrap complete."
