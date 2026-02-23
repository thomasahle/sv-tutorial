#!/usr/bin/env bash
# Download and install the Surfer waveform viewer web build.
#
# Usage:
#   scripts/setup-surfer.sh           # installs to public/surfer (default)
#   scripts/setup-surfer.sh <dir>     # installs to a custom directory

set -euo pipefail

DEST="${1:-public/surfer}"
ARTIFACT_URL="https://gitlab.com/surfer-project/surfer/-/jobs/artifacts/main/download?job=pages_build"

TMP=$(mktemp -d)
cleanup() { rm -rf "$TMP"; }
trap cleanup EXIT

echo "[setup-surfer] Downloading Surfer web build from GitLab CI..."

if command -v curl >/dev/null 2>&1; then
  curl -fL --progress-bar "$ARTIFACT_URL" -o "$TMP/surfer.zip"
elif command -v wget >/dev/null 2>&1; then
  wget -q --show-progress "$ARTIFACT_URL" -O "$TMP/surfer.zip"
else
  echo "Error: curl or wget is required." >&2
  exit 1
fi

echo "[setup-surfer] Extracting..."
unzip -q "$TMP/surfer.zip" -d "$TMP/extracted"

mkdir -p "$DEST"

# The artifact zip contains pages_build/ (full web app) and surfer_wasm/ (WASM only).
# We want pages_build/ — it has index.html, surfer.js, surfer_bg.wasm, etc.
if [ -d "$TMP/extracted/pages_build" ]; then
  cp -r "$TMP/extracted/pages_build/." "$DEST/"
elif [ -d "$TMP/extracted/public" ]; then
  cp -r "$TMP/extracted/public/." "$DEST/"
else
  cp -r "$TMP/extracted/." "$DEST/"
fi

echo "[setup-surfer] Done. Surfer installed at: $DEST"
echo "[setup-surfer] Verify with: ls $DEST/index.html"
