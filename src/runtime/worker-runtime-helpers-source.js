import { WORKER_NODE_COMPAT_SOURCE } from './worker-node-compat-source.js';

export const WORKER_RUNTIME_HELPERS_SOURCE = String.raw`
${WORKER_NODE_COMPAT_SOURCE}

// Minimal POSIX path shim — used as the return value of require('path') for
// Emscripten builds that call require('path') unconditionally at module level.
var WORKER_PATH_SHIM = {
  sep: '/',
  isAbsolute: function(p) { return String(p).charAt(0) === '/'; },
  normalize: function(p) { return String(p).replace(/\/+/g, '/').replace(/(.)\/$/, '$1') || '/'; },
  dirname: function(p) { var s = String(p); var i = s.lastIndexOf('/'); return i <= 0 ? '/' : s.slice(0, i); },
  basename: function(p, ext) { var b = String(p).split('/').pop() || ''; return ext && b.slice(-ext.length) === ext ? b.slice(0, -ext.length) : b; },
  extname: function(p) { var b = String(p).split('/').pop() || ''; var i = b.lastIndexOf('.'); return i <= 0 ? '' : b.slice(i); },
  join: function() { return Array.prototype.slice.call(arguments).join('/').replace(/\/+/g, '/'); },
  join2: function(a, b) { return (String(a) + '/' + String(b)).replace(/\/+/g, '/'); },
  resolve: function() { return Array.prototype.slice.call(arguments).join('/').replace(/\/+/g, '/'); }
};
WORKER_PATH_SHIM.posix = WORKER_PATH_SHIM;

function isNoderawfsScript(scriptText) {
  var text = String(scriptText || '');
  return (
    text.indexOf('NODERAWFS is currently only supported') >= 0 ||
    text.indexOf('var nodePath=require(') >= 0
  );
}

async function fetchScriptText(url) {
  try {
    var response = await fetch(url);
    if (!response.ok) return null;
    return await response.text();
  } catch(_) {
    return null;
  }
}

function normalizeFetchedScriptText(scriptText, jsUrl) {
  var text = String(scriptText || '');
  if (!text) return text;

  // Strip UTF-8 BOM if present.
  if (text.charCodeAt(0) === 0xFEFF) {
    text = text.slice(1);
  }

  // Eval() does not accept hashbang, but some JS wrappers include it.
  if (text.startsWith('#!')) {
    var newline = text.indexOf('\n');
    text = newline === -1 ? '' : text.slice(newline + 1);
  }

  var trimmed = text.trimStart().toLowerCase();
  if (trimmed.startsWith('<!doctype') || trimmed.startsWith('<html')) {
    throw new Error('Tool script resolved to HTML instead of JS: ' + String(jsUrl || ''));
  }

  return text;
}

function installPathRequireOnly(pathShim) {
  if (typeof self.require !== 'undefined') return;
  self.require = function(mod) {
    if (mod === 'path' || mod === 'node:path') return pathShim;
    throw new Error('require(\'' + mod + '\') is not available in browser worker');
  };
}

function injectCallMainExportShim(scriptText) {
  var text = String(scriptText || '');
  if (!text || text.indexOf('function callMain(') < 0) return text;
  if (text.indexOf('__svt_callMain') >= 0) return text;

  return text + "\\n;try{if(typeof callMain==='function'&&typeof self!=='undefined'&&typeof self.__svt_callMain!=='function'){self.__svt_callMain=callMain;}}catch(_){}\\n";
}

async function loadEmscriptenTool(opts) {
  var options = opts || {};
  var jsUrl = options.jsUrl;
  var pathShim = options.pathShim || WORKER_PATH_SHIM;
  var makeFs = (typeof options.makeFs === 'function') ? options.makeFs : null;
  var onStdout = (typeof options.onStdout === 'function') ? options.onStdout : function() {};
  var onStderr = (typeof options.onStderr === 'function') ? options.onStderr : function() {};
  var onMode = (typeof options.onMode === 'function') ? options.onMode : null;
  var beforeEval = (typeof options.beforeEval === 'function') ? options.beforeEval : null;
  var afterEval = (typeof options.afterEval === 'function') ? options.afterEval : null;

  var scriptText = await fetchScriptText(jsUrl);
  if (!scriptText) {
    throw new Error('Failed to load tool script: ' + String(jsUrl || ''));
  }
  scriptText = normalizeFetchedScriptText(scriptText, jsUrl);
  scriptText = injectCallMainExportShim(scriptText);
  var isNoderawfs = !!scriptText && isNoderawfsScript(scriptText);
  var fsBundle = null;

  if (isNoderawfs) {
    if (onMode) onMode('noderawfs');
    if (makeFs) fsBundle = makeFs();
    setupWorkerNodeCompat({
      pathShim: pathShim,
      fsApi: fsBundle && fsBundle.nodeApi ? fsBundle.nodeApi : null,
      onStdout: onStdout,
      onStderr: onStderr
    });
  } else {
    if (onMode) onMode('browser');
    installPathRequireOnly(pathShim);
  }
  if (beforeEval) beforeEval();
  try {
    (0, eval)(scriptText);
  } catch (error) {
    var message = String((error && error.message) || error || 'unknown eval error');
    throw new Error('Failed to evaluate tool script ' + String(jsUrl || '') + ': ' + message);
  }
  if (afterEval) afterEval();

  return {
    scriptText: scriptText,
    isNoderawfs: isNoderawfs,
    fs: fsBundle
  };
}
`;
