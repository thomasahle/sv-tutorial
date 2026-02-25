export const OFFLINE_APP_CACHE_PREFIX = 'svt-app-';
export const OFFLINE_RUNTIME_CACHE = 'svt-runtime-v1';
export const OFFLINE_STATE_KEY = 'svt:offline-ready-v1';
export const OFFLINE_READY_SENTINEL_RELATIVE_PATH = '__offline__/ready';

export const HEAVY_STATIC_PREFIXES = ['circt/', 'surfer/', 'z3/', 'pyodide/'];

export const SURFER_RUNTIME_PATHS = [
  'surfer/index.html',
  'surfer/surfer.js',
  'surfer/surfer_bg.wasm',
  'surfer/integration.js',
  'surfer/manifest.json',
  'surfer/sw.js',
];

export const LOCAL_RUNTIME_PATHS = [
  'circt/circt-verilog.js',
  'circt/circt-verilog.wasm',
  'circt/circt-sim.js',
  'circt/circt-sim.wasm',
  'circt/circt-bmc.js',
  'circt/circt-bmc.wasm',
  'circt/circt-sim-vpi.js',
  'circt/circt-sim-vpi.wasm',
  'circt/circt-lec.js',
  'circt/circt-lec.wasm',
  'circt/uvm-core/uvm-manifest.json',
  'z3/z3-built.js',
  'z3/z3-built.wasm',
  ...SURFER_RUNTIME_PATHS,
];

export const PYODIDE_MANIFEST_RELATIVE_PATH = 'pyodide/pyodide-manifest.json';
export const UVM_MANIFEST_RELATIVE_PATH = 'circt/uvm-core/uvm-manifest.json';

export const PYODIDE_COMPANION_FILES = [
  'pyodide.js',
  'pyodide.mjs',
  'pyodide.asm.js',
  'pyodide.asm.wasm',
  'python_stdlib.zip',
  'pyodide-lock.json',
  'repodata.json',
  'package.json',
];

export function normalizeBasePath(rawBase) {
  const base = String(rawBase || '').trim();
  if (!base || base === '/' || base === './' || base === '.') return '/';
  const withLeading = base.startsWith('/') ? base : `/${base}`;
  return withLeading.endsWith('/') ? withLeading : `${withLeading}/`;
}

export function joinBasePath(basePath, relPath) {
  const base = normalizeBasePath(basePath);
  const rel = String(relPath || '').replace(/^\/+/, '');
  return `${base}${rel}`;
}

export function dedupeStrings(values) {
  return Array.from(new Set((values || []).filter(Boolean).map((v) => String(v))));
}

export function offlineReadySentinelUrl(basePath = '/') {
  return joinBasePath(basePath, OFFLINE_READY_SENTINEL_RELATIVE_PATH);
}

export function z3WasmFromScriptUrl(z3ScriptUrl) {
  const url = String(z3ScriptUrl || '');
  if (!url) return '';
  if (url.endsWith('.js')) return `${url.slice(0, -3)}.wasm`;
  return '';
}

export function siblingUrls(baseFileUrl, fileNames) {
  const base = String(baseFileUrl || '');
  if (!base) return [];
  let baseDirUrl = '';
  try {
    baseDirUrl = new URL('./', base).href;
  } catch {
    return [];
  }
  return (fileNames || []).map((name) => {
    try {
      return new URL(String(name), baseDirUrl).href;
    } catch {
      return '';
    }
  }).filter(Boolean);
}

export function buildConfiguredRuntimeUrls({ basePath = '/', runtimeConfig = null, z3ScriptUrl = '' } = {}) {
  const urls = [];
  const cfg = runtimeConfig || {};
  const toolchain = cfg.toolchain || {};

  for (const toolName of Object.keys(toolchain)) {
    const tool = toolchain[toolName] || {};
    if (tool.js) urls.push(String(tool.js));
    if (tool.wasm) urls.push(String(tool.wasm));
  }

  if (cfg.pyodideUrl) {
    const pyodideUrl = String(cfg.pyodideUrl);
    urls.push(pyodideUrl);
    urls.push(...siblingUrls(pyodideUrl, PYODIDE_COMPANION_FILES));
  }

  if (z3ScriptUrl) {
    urls.push(String(z3ScriptUrl));
    const z3WasmUrl = z3WasmFromScriptUrl(z3ScriptUrl);
    if (z3WasmUrl) urls.push(z3WasmUrl);
  }

  urls.push(...LOCAL_RUNTIME_PATHS.map((path) => joinBasePath(basePath, path)));
  urls.push(joinBasePath(basePath, PYODIDE_MANIFEST_RELATIVE_PATH));

  return dedupeStrings(urls);
}
