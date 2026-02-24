#!/usr/bin/env bash
# Download and install the Surfer waveform viewer web build.
#
# Usage:
#   scripts/setup-surfer.sh           # installs to public/surfer (default)
#   scripts/setup-surfer.sh <dir>     # installs to a custom directory

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
source "$ROOT_DIR/scripts/toolchain.lock.sh"

DEST="${1:-public/surfer}"
ARTIFACT_URL="${SURFER_ARTIFACT_URL:-$SURFER_ARTIFACT_URL_LOCKED}"
ARTIFACT_SHA256="${SURFER_ARTIFACT_SHA256:-$SURFER_ARTIFACT_SHA256_LOCKED}"

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

if [[ -n "$ARTIFACT_SHA256" ]]; then
  actual_sha256="$(shasum -a 256 "$TMP/surfer.zip" | awk '{print $1}')"
  if [[ "$actual_sha256" != "$ARTIFACT_SHA256" ]]; then
    echo "[setup-surfer] SHA256 mismatch for downloaded artifact." >&2
    echo "[setup-surfer] expected: $ARTIFACT_SHA256" >&2
    echo "[setup-surfer] actual:   $actual_sha256" >&2
    exit 1
  fi
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

echo "[setup-surfer] Applying sv-tutorial Surfer integration hooks..."
node - "$DEST/index.html" "$DEST/integration.js" <<'NODE'
const fs = require('fs');

const [indexPath, integrationPath] = process.argv.slice(2);

function patchIndex(path) {
  let src = fs.readFileSync(path, 'utf8');

  src = src.replace(/import \{([^}]*)\} from '\.\/surfer\.js';/, (match, namesRaw) => {
    const names = namesRaw
      .split(',')
      .map((v) => v.trim())
      .filter(Boolean);
    if (!names.includes('waves_loaded')) {
      names.push('waves_loaded');
    }
    return `import { ${names.join(', ')} } from './surfer.js';`;
  });

  if (!src.includes('window.waves_loaded = waves_loaded;')) {
    const anchor = 'window.draw_text_arrow = draw_text_arrow;';
    if (!src.includes(anchor)) {
      throw new Error(`could not find draw_text_arrow assignment in ${path}`);
    }
    src = src.replace(anchor, `${anchor}\n        window.waves_loaded = waves_loaded;`);
  }

  fs.writeFileSync(path, src);
}

function patchIntegration(path) {
  const shim = `// sv-tutorial Surfer integration shim
// Provides a stable postMessage bridge and readiness events expected by the app.

function register_message_listener() {
  const pending = [];
  let wavesLoadedNotified = false;
  let engineReadyNotified = false;

  function notifyParent(type, payload = {}) {
    if (window.parent && window.parent !== window) {
      window.parent.postMessage({ source: 'surfer', type, ...payload }, '*');
    }
  }

  function canInject() {
    return typeof window.inject_message === 'function';
  }

  function flushPendingMessages() {
    if (!canInject()) return;
    while (pending.length > 0) {
      const msg = pending.shift();
      window.inject_message(msg);
    }
    if (!engineReadyNotified) {
      engineReadyNotified = true;
      notifyParent('engine-ready');
    }
  }

  function queueOrInjectMessage(encodedMessage) {
    if (canInject()) {
      window.inject_message(encodedMessage);
    } else {
      pending.push(encodedMessage);
    }
  }

  async function notifyIfWavesLoaded() {
    if (wavesLoadedNotified) return;
    if (typeof window.waves_loaded !== 'function') return;
    try {
      const loaded = await window.waves_loaded();
      if (!loaded) return;
      wavesLoadedNotified = true;
      notifyParent('waves-loaded');
    } catch {
      // Ignore transient readiness errors while Surfer boots.
    }
  }

  function injectSurferMessage(message) {
    queueOrInjectMessage(JSON.stringify(message));
  }

  window.addEventListener('message', (event) => {
    const decoded = event.data;
    if (!decoded || typeof decoded !== 'object') return;
    switch (decoded.command) {
      case 'LoadUrl': {
        wavesLoadedNotified = false;
        injectSurferMessage({ LoadWaveformFileFromUrl: [decoded.url, 'Clear'] });
        break;
      }
      case 'ToggleMenu': {
        queueOrInjectMessage(JSON.stringify('ToggleMenu'));
        break;
      }
      case 'InjectMessage': {
        if (typeof decoded.message === 'string') {
          queueOrInjectMessage(decoded.message);
        }
        break;
      }
      default:
        break;
    }
  });

  notifyParent('listener-ready');

  setInterval(() => {
    flushPendingMessages();
    notifyIfWavesLoaded();
  }, 100);
}
`;
  fs.writeFileSync(path, shim);
}

patchIndex(indexPath);
patchIntegration(integrationPath);
NODE

echo "[setup-surfer] Done. Surfer installed at: $DEST"
echo "[setup-surfer] Verify with: ls $DEST/index.html"
