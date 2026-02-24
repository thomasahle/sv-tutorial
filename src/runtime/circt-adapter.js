import { CIRCT_FORK_REPO, getCirctRuntimeConfig } from './circt-config.js';
import COCOTB_SHIM from './cocotb-shim.py?raw';

function filename(path) {
  const idx = path.lastIndexOf('/');
  return idx === -1 ? path : path.slice(idx + 1);
}

function ext(path) {
  const base = filename(path);
  const idx = base.lastIndexOf('.');
  return idx === -1 ? '' : base.slice(idx).toLowerCase();
}

function normalizePath(path) {
  if (!path) return '/workspace/input.sv';
  if (path.startsWith('/workspace/')) return path;
  if (path.startsWith('/')) return `/workspace${path}`;
  return `/workspace/${path}`;
}

function dirname(path) {
  const idx = path.lastIndexOf('/');
  if (idx <= 0) return '/';
  return path.slice(0, idx);
}

function joinPosix(base, rel) {
  if (!rel) return base;
  if (rel.startsWith('/')) return rel;
  const stack = base.split('/').filter(Boolean);
  for (const part of rel.split('/')) {
    if (!part || part === '.') continue;
    if (part === '..') {
      stack.pop();
    } else {
      stack.push(part);
    }
  }
  return `/${stack.join('/')}`;
}

function sourcePathsFromWorkspace(files) {
  return Object.keys(files)
    .filter((path) => ['.sv', '.v'].includes(ext(path)))
    .sort();
}

function compileRootSourcePaths(files) {
  const svPaths = sourcePathsFromWorkspace(files);
  const fileSet = new Set(Object.keys(files));
  const includedSources = new Set();

  for (const path of svPaths) {
    const content = files[path];
    if (typeof content !== 'string') continue;

    const includePattern = /^\s*`include\s+"([^"]+)"/gm;
    for (const match of content.matchAll(includePattern)) {
      const includePath = match[1];
      if (!includePath) continue;

      const resolved = joinPosix(dirname(path), includePath);
      if (!fileSet.has(resolved)) continue;
      if (!['.sv', '.v'].includes(ext(resolved))) continue;
      includedSources.add(resolved);
    }
  }

  const roots = svPaths.filter((path) => !includedSources.has(path));
  return roots.length ? roots : svPaths;
}

function containsPath(files, basename) {
  return Object.keys(files).some((path) => filename(path).toLowerCase() === basename.toLowerCase());
}

function moduleNamesFromWorkspace(files) {
  const names = new Set();
  for (const path of sourcePathsFromWorkspace(files)) {
    const content = files[path];
    if (typeof content !== 'string') continue;
    const pattern = /^\s*module\s+([A-Za-z_]\w*)\b/gm;
    for (const match of content.matchAll(pattern)) {
      if (match[1]) names.add(match[1]);
    }
  }
  return names;
}

function needsUvmLibrary(files) {
  return Object.values(files).some((content) =>
    typeof content === 'string' &&
    (/`include\s+"uvm_macros\.svh"/.test(content) ||
      /\bimport\s+uvm_pkg::\*/.test(content) ||
      /`uvm_[A-Za-z0-9_]+/.test(content))
  );
}

function hasVcdSignalDefinitions(vcdText) {
  return typeof vcdText === 'string' && /\$var\b/.test(vcdText);
}

// circt-sim inlines child-instance ports as dotted names (e.g. "dut.sum") into
// the parent scope alongside the parent wire ("result"). Strip those duplicates
// so the waveform viewer only shows the canonical wire name.
function removeInlinedPortsFromVcd(vcd) {
  if (typeof vcd !== 'string') return vcd;
  const lines = vcd.split('\n');
  const skipIds = new Set();

  for (const line of lines) {
    const m = line.match(/\$var\s+\S+\s+\d+\s+(\S+)\s+(\S+)(?:\s+\[\S+\])?\s+\$end/);
    if (m && m[2].includes('.')) skipIds.add(m[1]);
  }
  if (skipIds.size === 0) return vcd;

  return lines.filter((line) => {
    const t = line.trim();
    if (/\$var/.test(t)) {
      const m = t.match(/\$var\s+\S+\s+\d+\s+(\S+)/);
      if (m && skipIds.has(m[1])) return false;
    }
    const bm = t.match(/^b\S+\s+(\S+)$/);
    if (bm && skipIds.has(bm[1])) return false;
    const sm = t.match(/^[01xzXZ](\S+)$/);
    if (sm && skipIds.has(sm[1])) return false;
    return true;
  }).join('\n');
}

function shellQuote(arg) {
  const text = String(arg);
  if (text.length === 0) return "''";
  if (/^[A-Za-z0-9_./:=+,-]+$/.test(text)) return text;
  return `'${text.replace(/'/g, `'\\''`)}'`;
}

function formatCommand(tool, args = []) {
  return `$ ${[tool, ...args].map(shellQuote).join(' ')}`;
}

function appendNonZeroExit(logs, tool, exitCode, onLog = null) {
  if (exitCode !== 0) {
    const line = `# ${tool} exit code: ${exitCode}`;
    logs.push(line);
    if (typeof onLog === 'function') onLog(line);
  }
}

function removeFlag(args, flag) {
  return (args || []).filter((arg) => arg !== flag);
}

function forceInterpretSimMode(args) {
  const inArgs = Array.isArray(args) ? args : [];
  const out = [];

  for (let i = 0; i < inArgs.length; i++) {
    const arg = inArgs[i];
    if (arg === '--mode') {
      i += 1; // Skip explicit mode value.
      continue;
    }
    if (arg.startsWith('--mode=')) continue;
    if (arg === '--compiled') {
      i += 1; // Skip compiled module path.
      continue;
    }
    if (arg.startsWith('--compiled=')) continue;
    out.push(arg);
  }

  out.push('--mode', 'interpret');
  return out;
}

const UVM_FS_ROOT = '/circt/uvm-core';
const UVM_INCLUDE_ROOT = `${UVM_FS_ROOT}/src`;

function pickTopModules(files, fallbackTop) {
  const moduleNames = moduleNamesFromWorkspace(files);

  if (containsPath(files, 'hdl_top.sv') && containsPath(files, 'hvl_top.sv')) {
    return ['hdl_top', 'hvl_top'];
  }
  if (containsPath(files, 'tb_top.sv') || moduleNames.has('tb_top')) {
    return ['tb_top'];
  }
  if (containsPath(files, 'tb.sv')) {
    return ['tb'];
  }
  if (fallbackTop && moduleNames.has(fallbackTop)) {
    return [fallbackTop];
  }
  if (containsPath(files, 'top.sv')) {
    return ['top'];
  }

  if (moduleNames.size) {
    return [Array.from(moduleNames).sort()[0]];
  }

  const firstSource = sourcePathsFromWorkspace(files)[0] || 'top.sv';
  return [filename(firstSource).replace(/\.[^.]+$/, '') || 'top'];
}

function isExitException(error) {
  const text = String(error?.message || error || '');
  return text.includes('ExitStatus') || text.includes('Program terminated') || text.includes('exit(');
}

function extractExitCode(error) {
  const text = String(error?.message || error || '');
  const patterns = [
    /ExitStatus[:( ]+(-?\d+)/i,
    /exit\((\-?\d+)\)/i,
    /status(?:=|:)\s*(-?\d+)/i,
    /code(?:=|:)\s*(-?\d+)/i
  ];

  for (const pattern of patterns) {
    const match = text.match(pattern);
    if (!match) continue;
    const code = Number.parseInt(match[1], 10);
    if (!Number.isNaN(code)) return code;
  }

  return 1;
}

const WORKER_SOURCE = String.raw`
const EXIT_PATTERNS = [
  /ExitStatus[:( ]+(-?\\d+)/i,
  /exit\\((\\-?\\d+)\\)/i,
  /status(?:=|:)\\s*(-?\\d+)/i,
  /code(?:=|:)\\s*(-?\\d+)/i
];

function extractExitCode(error) {
  const text = String((error && error.message) || error || '');
  for (const pattern of EXIT_PATTERNS) {
    const match = text.match(pattern);
    if (!match) continue;
    const code = Number.parseInt(match[1], 10);
    if (!Number.isNaN(code)) return code;
  }
  return 1;
}

function isExitException(error) {
  const text = String((error && error.message) || error || '');
  return text.includes('ExitStatus') || text.includes('Program terminated') || text.includes('exit(');
}

function dirname(path) {
  const idx = path.lastIndexOf('/');
  if (idx <= 0) return '/';
  return path.slice(0, idx);
}

function ensureDir(FS, path) {
  if (!path || path === '/') return;
  const parts = path.split('/').filter(Boolean);
  let cur = '';
  for (const part of parts) {
    cur += '/' + part;
    try {
      FS.mkdir(cur);
    } catch {
      // Already exists.
    }
  }
}

function writeWorkspaceFiles(FS, files) {
  for (const [path, content] of Object.entries(files || {})) {
    ensureDir(FS, dirname(path));
    if (typeof content === 'string') {
      FS.writeFile(path, content, { encoding: 'utf8' });
    } else {
      FS.writeFile(path, content);
    }
  }
}

function readWorkspaceFiles(FS, paths) {
  const out = {};
  for (const path of paths || []) {
    try {
      out[path] = FS.readFile(path, { encoding: 'utf8' });
    } catch {
      // Ignore missing files.
    }
  }
  return out;
}

// Minimal POSIX path shim — used as the return value of require('path') for
// Emscripten builds that call require('path') unconditionally at module level.
var PATH_SHIM = {
  sep: '/',
  isAbsolute: function(p) { return String(p).charAt(0) === '/'; },
  normalize: function(p) { return String(p).replace(/\/+/g, '/').replace(/(.)\/$/, '$1') || '/'; },
  dirname: function(p) { var s = String(p); var i = s.lastIndexOf('/'); return i <= 0 ? '/' : s.slice(0, i); },
  basename: function(p, ext) { var b = String(p).split('/').pop() || ''; return ext && b.slice(-ext.length) === ext ? b.slice(0, -ext.length) : b; },
  extname: function(p) { var b = String(p).split('/').pop() || ''; var i = b.lastIndexOf('.'); return i <= 0 ? '' : b.slice(i); },
  join: function() { return Array.prototype.slice.call(arguments).join('/').replace(/\/+/g, '/'); },
  join2: function(a, b) { return (String(a) + '/' + String(b)).replace(/\/+/g, '/'); },
  resolve: function() { return Array.prototype.slice.call(arguments).join('/').replace(/\/+/g, '/'); },
};
PATH_SHIM.posix = PATH_SHIM;

// In-memory filesystem for Emscripten NODERAWFS builds (like circt-sim.js).
// NODERAWFS replaces the entire Emscripten FS layer with direct Node.js fs calls.
// We provide a fake require('fs') that stores data in memory so that
// module.FS.writeFile / callMain / module.FS.readFile all share the same store.
function makeInMemFS(onStdoutChunk = null, onStderrChunk = null) {
  var store = {};
  var symlinks = {};
  var remoteFiles = {};
  var dirs = new Set([
    '/',
    '/dev',
    '/workspace',
    '/workspace/src',
    '/workspace/out',
    '/circt',
    '/circt/uvm-core',
    '/circt/uvm-core/src'
  ]);
  var fds = {};
  var nextFd = 3;
  var stdoutChunks = [];
  var stderrChunks = [];

  function ensureParentDir(path) {
    var parts = String(path).split('/').filter(Boolean);
    var cur = '';
    for (var i = 0; i < parts.length - 1; i++) { cur += '/' + parts[i]; dirs.add(cur); }
  }

  function makeStat(path) {
    path = String(path);
    if (symlinks[path]) {
      return {
        ino: 3, mode: 0o120777, size: symlinks[path].length, dev: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
        blksize: 4096, blocks: 1, atime: new Date(), mtime: new Date(), ctime: new Date(),
        isDirectory: function(){return false;}, isFile: function(){return false;},
        isSymbolicLink: function(){return true;}
      };
    }
    if (!dirs.has(path) && !store[path] && !remoteFiles[path]) {
      tryFetchIntoStore(path);
    }
    if (dirs.has(path)) {
      return { ino: 1, mode: 0o40755, size: 0, dev: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
               blksize: 4096, blocks: 0, atime: new Date(), mtime: new Date(), ctime: new Date(),
               isDirectory: function(){return true;}, isFile: function(){return false;},
               isSymbolicLink: function(){return false;} };
    }
    if (store[path] || remoteFiles[path]) {
      var size = store[path] ? store[path].length : 0;
      return { ino: 2, mode: 0o100644, size: size, dev: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
               blksize: 4096, blocks: Math.ceil(size / 512),
               atime: new Date(), mtime: new Date(), ctime: new Date(),
               isDirectory: function(){return false;}, isFile: function(){return true;},
               isSymbolicLink: function(){return false;} };
    }
    var e = new Error('ENOENT: no such file or directory, stat \'' + path + '\'');
    e.code = 'ENOENT'; throw e;
  }

  function tryFetchIntoStore(path) {
    path = String(path);
    if (store[path]) return true;
    try {
      var fetchUrl = remoteFiles[path] || path;
      var xhr = new XMLHttpRequest();
      xhr.open('GET', fetchUrl, false /* synchronous */);
      xhr.responseType = 'arraybuffer';
      xhr.send(null);
      if ((xhr.status === 200 || xhr.status === 0) && xhr.response) {
        var bytes = new Uint8Array(xhr.response);
        ensureParentDir(path);
        store[path] = bytes;
        return true;
      }
    } catch (fetchErr) {}
    return false;
  }

  var nodeApi = {
    readFileSync: function(path, opts) {
      path = String(path);
      if (!store[path]) {
        tryFetchIntoStore(path);
      }
      if (store[path]) {
        var enc = (typeof opts === 'string') ? opts : (opts && opts.encoding);
        return enc ? new TextDecoder().decode(store[path]) : store[path];
      }
      var e = new Error('ENOENT: no such file or directory, open \'' + path + '\'');
      e.code = 'ENOENT'; throw e;
    },
    existsSync: function(p) { return dirs.has(p) || !!store[p] || !!symlinks[p] || !!remoteFiles[p] || tryFetchIntoStore(p); },
    statSync: makeStat,
    lstatSync: makeStat,
    realpathSync: function(p) {
      const path = String(p);
      return symlinks[path] || path;
    },
    readlinkSync: function(p) {
      const path = String(p);
      if (symlinks[path]) return symlinks[path];
      const e = new Error('EINVAL: invalid argument, readlink \'' + path + '\'');
      e.code = 'EINVAL';
      throw e;
    },
    symlinkSync: function(target, path) {
      const link = String(path);
      ensureParentDir(link);
      symlinks[link] = String(target);
    },
    fstatSync: function(fd) {
      var f = fds[fd]; if (!f) { var e = new Error('EBADF'); e.code = 'EBADF'; throw e; }
      return makeStat(f.path);
    },
    readdirSync: function(path) {
      if (!dirs.has(path)) { var e = new Error('ENOENT: ' + path); e.code = 'ENOENT'; throw e; }
      var prefix = path === '/' ? '/' : path + '/';
      var entries = new Set();
      dirs.forEach(function(d) {
        if (d !== path && d.startsWith(prefix)) {
          var rel = d.slice(prefix.length);
          if (rel.indexOf('/') < 0) entries.add(rel);
        }
      });
      Object.keys(store).forEach(function(f) {
        if (f.startsWith(prefix)) {
          var rel = f.slice(prefix.length);
          if (rel.indexOf('/') < 0) entries.add(rel);
        }
      });
      Object.keys(remoteFiles).forEach(function(f) {
        if (f.startsWith(prefix)) {
          var rel = f.slice(prefix.length);
          if (rel.indexOf('/') < 0) entries.add(rel);
        }
      });
      return Array.from(entries);
    },
    mkdirSync: function(p) { dirs.add(String(p)); },
    rmdirSync: function(p) { dirs.delete(p); },
    unlinkSync: function(p) { delete store[p]; delete symlinks[p]; },
    renameSync: function(from, to) {
      if (store[from]) {
        store[to] = store[from];
        delete store[from];
      }
      if (symlinks[from]) {
        symlinks[to] = symlinks[from];
        delete symlinks[from];
      }
    },
    chmodSync: function() {},
    chownSync: function() {},
    utimesSync: function() {},
    fsyncSync: function() {},
    ftruncateSync: function(fd, len) {
      var f = fds[fd]; var d = store[f.path] || new Uint8Array(0);
      store[f.path] = len <= d.length ? d.subarray(0, len) : (function(){ var g = new Uint8Array(len); g.set(d); return g; })();
    },
    openSync: function(path, flags) {
      path = String(path);
      var writable;
      if (typeof flags === 'string') {
        writable = flags.indexOf('w') >= 0 || flags.indexOf('a') >= 0 || flags.indexOf('+') >= 0;
      } else {
        var numericFlags = Number(flags) || 0;
        var accessMode = numericFlags & 3; // O_RDONLY=0, O_WRONLY=1, O_RDWR=2
        writable = accessMode !== 0 || !!(numericFlags & 64) || !!(numericFlags & 512) || !!(numericFlags & 1024);
      }
      if (writable) {
        store[path] = new Uint8Array(0);
        ensureParentDir(path);
      } else {
        if (!store[path] && remoteFiles[path]) {
          tryFetchIntoStore(path);
        }
        if (!store[path] && !dirs.has(path) && !remoteFiles[path] && !tryFetchIntoStore(path)) {
          var e = new Error('ENOENT: ' + path);
          e.code = 'ENOENT';
          throw e;
        }
      }
      var fd = nextFd++; fds[fd] = { path: path, pos: 0 }; return fd;
    },
    closeSync: function(fd) { delete fds[fd]; },
    readSync: function(fd, buf, bufOffset, length, position) {
      if (fd === 0) return 0;
      var f = fds[fd];
      if (!store[f.path] && remoteFiles[f.path]) {
        tryFetchIntoStore(f.path);
      }
      var data = store[f.path] || new Uint8Array(0);
      var pos = position != null ? position : f.pos;
      var avail = Math.min(length, data.length - pos);
      if (avail <= 0) return 0;
      buf.set(data.subarray(pos, pos + avail), bufOffset);
      if (position == null) f.pos += avail;
      return avail;
    },
    writeSync: function(fd, buf, bufOffset, length, position) {
      var src;
      if (typeof buf === 'string') {
        src = new TextEncoder().encode(buf);
      } else if (ArrayBuffer.isView(buf)) {
        src = new Uint8Array(buf.buffer, buf.byteOffset, buf.byteLength);
      } else if (buf instanceof ArrayBuffer) {
        src = new Uint8Array(buf);
      } else {
        src = new Uint8Array(0);
      }
      var start = Number.isFinite(bufOffset) ? Number(bufOffset) : 0;
      if (start < 0) start = 0;
      var writeLen = Number.isFinite(length) ? Number(length) : (src.length - start);
      if (writeLen < 0) writeLen = 0;
      var end = Math.min(src.length, start + writeLen);
      var chunk = src.subarray(start, end);
      if (fd === 1) {
        var text = new TextDecoder().decode(chunk);
        stdoutChunks.push(text);
        if (typeof onStdoutChunk === 'function') onStdoutChunk(text);
        return chunk.length;
      }
      if (fd === 2) {
        var text = new TextDecoder().decode(chunk);
        stderrChunks.push(text);
        if (typeof onStderrChunk === 'function') onStderrChunk(text);
        return chunk.length;
      }
      var f = fds[fd]; var pos = position != null ? position : f.pos;
      var data = store[f.path] || new Uint8Array(0);
      var needed = pos + chunk.length;
      if (needed > data.length) { var g = new Uint8Array(needed); g.set(data); data = g; }
      data.set(chunk, pos); store[f.path] = data;
      if (position == null) f.pos += chunk.length;
      return chunk.length;
    },
  };

  return {
    nodeApi: nodeApi,
    ensureDir: function(path) {
      dirs.add(String(path));
    },
    writeTextFile: function(path, text) {
      const filePath = String(path);
      ensureParentDir(filePath);
      store[filePath] = new TextEncoder().encode(String(text ?? ''));
    },
    readTextFile: function(path) {
      const filePath = String(path);
      if (!store[filePath]) {
        tryFetchIntoStore(filePath);
      }
      if (!store[filePath]) return null;
      return new TextDecoder().decode(store[filePath]);
    },
    registerRemoteFile: function(path, url) {
      path = String(path);
      remoteFiles[path] = String(url || path);
      ensureParentDir(path);
    },
    getStdout: function() { return stdoutChunks.join(''); },
    getStderr: function() { return stderrChunks.join(''); },
  };
}

var circtWorkerRuntimeReady = false;

function waitForRuntime(timeoutMs = 45000) {
  const start = Date.now();
  return new Promise((resolve, reject) => {
    const tick = () => {
      try {
        const module = self.Module;
        if (module && typeof self.callMain === 'function' && typeof module.callMain !== 'function') {
          module.callMain = self.callMain;
        }
        if (module && !module.FS && self.FS) {
          module.FS = self.FS;
        }

        if (
          circtWorkerRuntimeReady &&
          module &&
          typeof module.callMain === 'function' &&
          typeof module._main === 'function' &&
          module.FS &&
          typeof module.FS.writeFile === 'function' &&
          typeof module.FS.readFile === 'function'
        ) {
          resolve(module);
          return;
        }

        if (Date.now() - start >= timeoutMs) {
          reject(new Error('Emscripten runtime did not become ready in time'));
          return;
        }
        setTimeout(tick, 25);
      } catch (error) {
        reject(error);
      }
    };
    tick();
  });
}

self.onmessage = async (event) => {
  const req = event.data || {};
  const stdout = [];
  const stderr = [];
  const streamRemainder = { stdout: '', stderr: '' };

  function appendStreamLine(stream, line) {
    const text = String(line ?? '');
    if (stream === 'stdout') stdout.push(text);
    else stderr.push(text);
    self.postMessage({ type: 'stream', stream, line: text });
  }

  function appendStreamText(stream, text) {
    const piece = String(text ?? '');
    if (!piece) return;
    if (stream === 'stdout') stdout.push(piece);
    else stderr.push(piece);
    const combined = streamRemainder[stream] + piece;
    const parts = combined.split(/\r?\n/);
    streamRemainder[stream] = parts.pop() ?? '';
    for (const line of parts) {
      self.postMessage({ type: 'stream', stream, line });
    }
  }

  function flushStreamRemainders() {
    for (const stream of ['stdout', 'stderr']) {
      const tail = streamRemainder[stream];
      if (tail) {
        self.postMessage({ type: 'stream', stream, line: tail });
        streamRemainder[stream] = '';
      }
    }
  }

  try {
    self.Module = {
      noInitialRun: true,
      onRuntimeInitialized: () => {
        console.log('[circt-worker] onRuntimeInitialized fired');
        circtWorkerRuntimeReady = true;
      },
      print: (line) => appendStreamLine('stdout', line),
      printErr: (line) => appendStreamLine('stderr', line),
      locateFile: (path) => {
        if (path.endsWith('.wasm')) return req.wasmUrl;
        return path;
      },
      // Use streaming WASM compilation for all tools to avoid slow sync readBinary path.
      instantiateWasm: function(imports, callback) {
        console.log('[circt-worker] instantiateWasm called for', req.wasmUrl);
        WebAssembly.instantiateStreaming(fetch(req.wasmUrl), imports)
          .then(function(result) {
            console.log('[circt-worker] instantiateStreaming succeeded');
            callback(result.instance, result.module);
          })
          .catch(function(streamErr) {
            console.log('[circt-worker] instantiateStreaming failed, trying ArrayBuffer fallback:', String(streamErr));
            return fetch(req.wasmUrl)
              .then(function(r) { return r.arrayBuffer(); })
              .then(function(buf) { return WebAssembly.instantiate(buf, imports); })
              .then(function(result) {
                console.log('[circt-worker] ArrayBuffer instantiate succeeded');
                callback(result.instance, result.module);
              })
              .catch(function(abErr) {
                console.error('[circt-worker] both WASM instantiation paths failed:', String(abErr));
              });
          });
        return {};
      }
    };

    // Fetch the tool JS source to detect whether it was compiled with NODERAWFS=1.
    // NODERAWFS builds call require('path') unconditionally and fail in browser workers
    // unless we emulate a Node.js environment with an in-memory filesystem.
    let toolScript = null;
    try {
      const r = await fetch(req.jsUrl);
      if (r.ok) toolScript = await r.text();
    } catch (_) {}

    const isNoderawfs = !!toolScript && (
      toolScript.indexOf('NODERAWFS is currently only supported') >= 0 ||
      toolScript.indexOf('var nodePath=require(') >= 0
    );

    let inMemFS = null;
    if (isNoderawfs && toolScript) {
      // Emulate Node.js so ENVIRONMENT_IS_NODE=true, passing the NODERAWFS guard.
      // Provide an in-memory fs via require('fs') so all file I/O works in memory.
      console.log('[circt-worker] NODERAWFS detected, setting up Node.js emulation');
      inMemFS = makeInMemFS(
        (text) => appendStreamText('stdout', text),
        (text) => appendStreamText('stderr', text)
      );
      if (typeof self.__dirname === 'undefined') self.__dirname = '/';
      if (typeof self.__filename === 'undefined') self.__filename = '/tool.js';
      const proc = (typeof self.process === 'undefined' || self.process === null) ? {} : self.process;
      if (!proc.versions || typeof proc.versions !== 'object') proc.versions = {};
      if (!proc.versions.node) proc.versions.node = '18.0.0';
      if (typeof proc.version !== 'string') proc.version = 'v18.0.0';
      if (typeof proc.platform !== 'string') proc.platform = 'linux';
      if (!Array.isArray(proc.argv)) proc.argv = ['node', '/tool'];
      if (!proc.type) proc.type = 'worker';
      if (typeof proc.exitCode !== 'number') proc.exitCode = 0;
      // Emscripten calls process.exit(code) in Node.js mode on completion.
      // Throw an ExitStatus-shaped error so isExitException() catches it.
      if (typeof proc.exit !== 'function') {
        proc.exit = function(code) {
          throw { name: 'ExitStatus', message: 'exit(' + (code | 0) + ')', status: (code | 0) };
        };
      }
      if (typeof proc.on !== 'function') proc.on = function() { return proc; };
      if (!proc.stdout || typeof proc.stdout !== 'object') proc.stdout = {};
      if (!proc.stderr || typeof proc.stderr !== 'object') proc.stderr = {};
      proc.stdout.write = function(s) { appendStreamText('stdout', s); };
      proc.stdout.isTTY = false;
      proc.stderr.write = function(s) { appendStreamText('stderr', s); };
      proc.stderr.isTTY = false;
      proc.stdin = proc.stdin || null;
      if (!proc.env || typeof proc.env !== 'object') proc.env = {};
      if (typeof proc.cwd !== 'function') proc.cwd = function() { return '/workspace'; };
      proc.binding = function(name) {
        if (name === 'constants') {
          return {
            fs: {
              O_APPEND: 1024,
              O_CREAT: 64,
              O_EXCL: 128,
              O_NOCTTY: 256,
              O_RDONLY: 0,
              O_RDWR: 2,
              O_SYNC: 4096,
              O_TRUNC: 512,
              O_WRONLY: 1,
              O_NOFOLLOW: 131072
            }
          };
        }
        throw new Error('process.binding(' + String(name) + ') is not available');
      };
      self.process = proc;
      if (typeof self.global === 'undefined') self.global = self;
      self.require = function(mod) {
        if (mod === 'path') return PATH_SHIM;
        if (mod === 'fs') return inMemFS.nodeApi;
        if (mod === 'crypto') return { randomBytes: function(n) { return crypto.getRandomValues(new Uint8Array(n)); } };
        if (mod === 'child_process') return { spawnSync: function() { return { status: 1, stdout: '', stderr: '' }; } };
        throw new Error('require(\'' + mod + '\') is not available in browser worker');
      };
      // eval in global scope (equivalent to importScripts for non-module scripts).
      console.log('[circt-worker] starting eval of tool script');
      (0, eval)(toolScript);
      console.log('[circt-worker] eval complete');
    } else {
      // Standard browser-worker mode. Add a path shim in case of unconditional require('path').
      if (typeof self.require === 'undefined') {
        self.require = function(mod) {
          if (mod === 'path') return PATH_SHIM;
          throw new Error('require(\'' + mod + '\') is not available in browser worker');
        };
      }
      importScripts(req.jsUrl);
    }

    console.log('[circt-worker] waiting for runtime...');
    const module = await waitForRuntime();
    if (typeof req.uvmManifestUrl === 'string' && req.uvmManifestUrl.length > 0) {
      const response = await fetch(req.uvmManifestUrl, { cache: 'force-cache' });
      if (!response.ok) {
        throw new Error('Failed to load UVM manifest: ' + response.status + ' ' + response.statusText);
      }
      const manifest = await response.json();
      const rootPath = (manifest && typeof manifest.rootPath === 'string' && manifest.rootPath.length > 0)
        ? manifest.rootPath
        : '/circt/uvm-core/src';
      const relPaths = Array.isArray(manifest && manifest.files) ? manifest.files : [];
      const srcBaseUrl = new URL('src/', req.uvmManifestUrl).href;
      for (const relRaw of relPaths) {
        if (typeof relRaw !== 'string') continue;
        const rel = relRaw.replace(/^\/+/, '');
        if (!rel || rel.includes('..')) continue;
        const fsPath = rootPath.replace(/\/+$/, '') + '/' + rel;
        const sourceUrl = new URL(rel, srcBaseUrl).href;
        if (inMemFS && typeof inMemFS.registerRemoteFile === 'function') {
          const srcResponse = await fetch(sourceUrl, { cache: 'force-cache' });
          if (!srcResponse.ok) {
            throw new Error('Failed to load UVM source: ' + sourceUrl);
          }
          const srcText = await srcResponse.text();
          inMemFS.writeTextFile(fsPath, srcText);
          continue;
        }
        if (module.FS && typeof module.FS.createLazyFile === 'function') {
          const idx = fsPath.lastIndexOf('/');
          const parent = idx <= 0 ? '/' : fsPath.slice(0, idx);
          const base = idx === -1 ? fsPath : fsPath.slice(idx + 1);
          ensureDir(module.FS, parent);
          try {
            module.FS.createLazyFile(parent, base, sourceUrl, true, false);
          } catch {
            // Ignore duplicate registrations.
          }
        }
      }
    }
    console.log('[circt-worker] runtime ready, writing files');
    if (inMemFS) {
      for (const [path, content] of Object.entries(req.files || {})) {
        inMemFS.writeTextFile(String(path), content);
      }
      for (const dir of req.createDirs || []) {
        inMemFS.ensureDir(String(dir));
      }
    } else {
      writeWorkspaceFiles(module.FS, req.files || {});
      for (const dir of req.createDirs || []) {
        ensureDir(module.FS, dir);
      }
    }

    console.log('[circt-worker] calling callMain with args:', req.args);
    let exitCode = 0;
    try {
      const ret = module.callMain(Array.isArray(req.args) ? req.args : []);
      if (typeof ret === 'number' && Number.isFinite(ret)) {
        exitCode = ret;
      }
    } catch (error) {
      if (!isExitException(error)) throw error;
      exitCode = extractExitCode(error);
    }
    console.log('[circt-worker] callMain done, exitCode:', exitCode);

    flushStreamRemainders();
    const files = inMemFS
      ? Object.fromEntries(
          (req.readFiles || [])
            .map((path) => [String(path), inMemFS.readTextFile(String(path))])
            .filter(([, content]) => typeof content === 'string')
        )
      : readWorkspaceFiles(module.FS, req.readFiles || []);
    self.postMessage({
      type: 'result',
      ok: true,
      exitCode,
      stdout: stdout.join('\n').trim(),
      stderr: stderr.join('\n').trim(),
      files
    });
  } catch (error) {
    flushStreamRemainders();
    self.postMessage({
      type: 'result',
      ok: false,
      exitCode: 1,
      stdout: stdout.join('\n').trim(),
      stderr: stderr.join('\n').trim(),
      files: {},
      error: String((error && error.stack) || (error && error.message) || error || 'unknown worker failure')
    });
  }
};
`;

let workerBlobUrl = null;

function getWorkerBlobUrl() {
  if (workerBlobUrl) return workerBlobUrl;
  const blob = new Blob([WORKER_SOURCE], { type: 'text/javascript' });
  workerBlobUrl = URL.createObjectURL(blob);
  return workerBlobUrl;
}

function runToolInWorker({
  jsUrl,
  wasmUrl,
  args,
  files,
  readFiles,
  createDirs = [],
  uvmManifestUrl = null,
  onOutput = null
}) {
  return new Promise((resolve, reject) => {
    const worker = new Worker(getWorkerBlobUrl());
    let sawStream = false;
    let timeout;
    const resetTimeout = () => {
      clearTimeout(timeout);
      timeout = setTimeout(() => {
        worker.terminate();
        reject(new Error(`${jsUrl}: tool invocation timed out`));
      }, 300000);
    };
    resetTimeout();

    worker.onmessage = (event) => {
      const payload = event.data || {};
      if (payload.type === 'stream') {
        sawStream = true;
        resetTimeout();
        if (typeof onOutput === 'function') {
          const stream = payload.stream === 'stderr' ? 'stderr' : 'stdout';
          onOutput({ stream, line: String(payload.line ?? '') });
        }
        return;
      }
      clearTimeout(timeout);
      worker.terminate();
      const result = payload.type === 'result' ? payload : payload;
      if (!result.ok) {
        const prefix = result.error || 'tool invocation failed';
        const stderr = result.stderr ? ` :: ${result.stderr}` : '';
        reject(new Error(`${prefix}${stderr}`));
        return;
      }
      resolve({ ...result, streamed: sawStream });
    };

    worker.onerror = (event) => {
      clearTimeout(timeout);
      worker.terminate();
      reject(new Error(String(event?.message || 'worker crashed')));
    };

    worker.postMessage({ jsUrl, wasmUrl, args, files, readFiles, createDirs, uvmManifestUrl });
  });
}

// Lazy-initialised z3 Emscripten module — loaded on first BMC call.
let _z3ModPromise = null;

/**
 * Load z3-built.js as a plain <script> tag and call initZ3() to get the
 * Emscripten module.  We use the synchronous Z3_eval_smtlib2_string C API
 * via ccall rather than z3-solver's async wrapper (which requires pthreads /
 * SharedArrayBuffer threads that are unreliable in this context).
 *
 * z3-built.js must be a separate, unbundled file served at /z3/z3-built.js
 * so that its self-URL is correct for locating z3-built.wasm.
 */
function loadScriptOnce(src) {
  return new Promise((resolve, reject) => {
    const script = document.createElement('script');
    script.src = src;
    script.onload = resolve;
    script.onerror = () => reject(new Error(`Failed to load z3 script: ${src}`));
    document.head.appendChild(script);
  });
}

async function getZ3Module() {
  if (!_z3ModPromise) {
    _z3ModPromise = (async () => {
      if (!globalThis.initZ3) {
        await loadScriptOnce('/z3/z3-built.js');
      }
      return globalThis.initZ3();
    })();
  }
  return _z3ModPromise;
}

/**
 * Create a fresh z3 Emscripten module instance, bypassing the cached one.
 *
 * The browser's z3 WASM build sets an internal ABORT flag when the module
 * calls exit() (which can happen after Z3_eval_smtlib2_string completes its
 * run). That flag is a closure variable — not resettable from outside — so
 * any subsequent ccall on the same instance throws "Program terminated with
 * exit(1)". A fresh instance has no such state.
 */
async function getFreshZ3Module() {
  if (!globalThis.initZ3) {
    await loadScriptOnce('/z3/z3-built.js');
  }
  return globalThis.initZ3();
}

/**
 * Evaluate an SMT-LIB 2 string with z3 and return the output string.
 * Uses the synchronous Z3_eval_smtlib2_string C API via Emscripten ccall.
 */
async function evalSmtlib(smtlibText, { produceModels = false, em: emOverride = null } = {}) {
  const em = emOverride ?? await getZ3Module();
  const cfg = em.ccall('Z3_mk_config', 'number', [], []);
  if (produceModels) {
    em.ccall('Z3_set_param_value', null, ['number', 'string', 'string'], [cfg, 'model', 'true']);
  }
  const ctx = em.ccall('Z3_mk_context', 'number', ['number'], [cfg]);
  em.ccall('Z3_del_config', null, ['number'], [cfg]);
  try {
    return em.ccall('Z3_eval_smtlib2_string', 'string', ['number', 'string'], [ctx, smtlibText]);
  } finally {
    em.ccall('Z3_del_context', null, ['number'], [ctx]);
  }
}

// Names that indicate a testbench rather than synthesisable design files.
const TESTBENCH_NAMES = new Set(['tb', 'tb_top', 'hvl_top', 'testbench', 'test_top']);

function isTestbench(path) {
  const base = filename(path).toLowerCase().replace(/\.sv[h]?$/, '');
  return TESTBENCH_NAMES.has(base);
}

function toAbsoluteUrl(rawUrl) {
  try {
    return new URL(rawUrl, window.location.href).href;
  } catch {
    return rawUrl;
  }
}

function getUvmManifestUrl() {
  return toAbsoluteUrl(`${import.meta.env.BASE_URL}circt/uvm-core/uvm-manifest.json`);
}

// ── Cocotb worker ─────────────────────────────────────────────────────────────
// Self-contained Web Worker source for running cocotb tests via Pyodide +
// a VPI-capable, Asyncify-transformed circt-sim WASM.
//
// circt-sim-vpi may be built with NODERAWFS=1 (the Emscripten default).
// In that case importScripts() fails immediately because the script calls
// require('path') at module level.  We detect this and fall back to eval()
// with a fake Node.js environment backed by an in-memory filesystem, exactly
// like WORKER_SOURCE does for the regular circt-sim.

const COCOTB_WORKER_SOURCE = String.raw`
var VPI = {
  cbValueChange: 1,
  cbStartOfSimulation: 11,
  cbEndOfSimulation: 12,
  cbAfterDelay: 9,
  vpiFinish: 66,
  vpiIntVal: 1,
  vpiSimTime: 1,
};

function wsWriteString(M, str) {
  var bytes = new TextEncoder().encode(str + '\0');
  var ptr = M._malloc(bytes.length);
  M.HEAPU8.set(bytes, ptr);
  return ptr;
}

function wsMakeVpiTime(M, fsBI) {
  var ps = BigInt(fsBI) / 1000n;
  var hi = Number(ps >> 32n) >>> 0;
  var lo = Number(ps & 0xFFFFFFFFn) >>> 0;
  var ptr = M._malloc(20);
  M.setValue(ptr +  0, VPI.vpiSimTime, 'i32');
  M.setValue(ptr +  4, hi,             'i32');
  M.setValue(ptr +  8, lo,             'i32');
  M.setValue(ptr + 12, 0.0,            'double');
  return ptr;
}

function wsMakeCbData(M, reason, cbRtn, obj, time, userData) {
  var ptr = M._malloc(28);
  M.setValue(ptr +  0, reason   || 0, 'i32');
  M.setValue(ptr +  4, cbRtn    || 0, 'i32');
  M.setValue(ptr +  8, obj      || 0, 'i32');
  M.setValue(ptr + 12, time     || 0, 'i32');
  M.setValue(ptr + 16, 0,             'i32');
  M.setValue(ptr + 20, 0,             'i32');
  M.setValue(ptr + 24, userData || 0, 'i32');
  return ptr;
}

function wsMakeVpiValue(M, intVal) {
  var ptr = M._malloc(12);
  M.setValue(ptr + 0, VPI.vpiIntVal, 'i32');
  M.setValue(ptr + 4, intVal || 0,   'i32');
  M.setValue(ptr + 8, 0,             'i32');
  return ptr;
}

function wsReadVpiIntValue(M, ptr) {
  return M.getValue(ptr + 4, 'i32');
}

function wsRegisterVpiTrigger(M, spec, cbFnPtr) {
  if (spec.type === 'timer') {
    var timePtr = wsMakeVpiTime(M, BigInt(spec.fs));
    var cbData = wsMakeCbData(M, VPI.cbAfterDelay, cbFnPtr, 0, timePtr, spec.id);
    var handle = M._vpi_register_cb(cbData);
    M._free(timePtr);
    M._free(cbData);
    return handle;
  }
  if (spec.type === 'rising_edge' || spec.type === 'falling_edge') {
    var namePtr = wsWriteString(M, spec.signal);
    var sigHandle = M._vpi_handle_by_name(namePtr, 0);
    M._free(namePtr);
    var cbData2 = wsMakeCbData(M, VPI.cbValueChange, cbFnPtr, sigHandle, 0, spec.id);
    var handle2 = M._vpi_register_cb(cbData2);
    M._free(cbData2);
    return handle2;
  }
  return 0;
}

function wsVpiGetSignalValue(M, name) {
  var namePtr = wsWriteString(M, name);
  var handle = M._vpi_handle_by_name(namePtr, 0);
  M._free(namePtr);
  if (!handle) return 0;
  var vp = wsMakeVpiValue(M, 0);
  M._vpi_get_value(handle, vp);
  var result = wsReadVpiIntValue(M, vp);
  M._free(vp);
  return result;
}

function wsVpiSetSignalValue(M, name, val) {
  var namePtr = wsWriteString(M, name);
  var handle = M._vpi_handle_by_name(namePtr, 0);
  M._free(namePtr);
  if (!handle) return;
  var vp = wsMakeVpiValue(M, val);
  M._vpi_put_value(handle, vp, 0, 0);
  M._free(vp);
}

function isExitException(err) {
  var t = String((err && err.message) || err || '');
  return t.includes('ExitStatus') || t.includes('Program terminated') || t.includes('exit(');
}

// ── NODERAWFS shims ──────────────────────────────────────────────────────────
// Used when circt-sim-vpi is built with -sNODERAWFS=1.

var SIM_PATH_SHIM = {
  sep: '/',
  isAbsolute: function(p) { return String(p).charAt(0) === '/'; },
  normalize: function(p) { return String(p).replace(/\/+/g, '/').replace(/(.)\/$/, '$1') || '/'; },
  dirname: function(p) { var s = String(p); var i = s.lastIndexOf('/'); return i <= 0 ? '/' : s.slice(0, i); },
  basename: function(p, ext) { var b = String(p).split('/').pop() || ''; return ext && b.slice(-ext.length) === ext ? b.slice(0, -ext.length) : b; },
  extname: function(p) { var b = String(p).split('/').pop() || ''; var i = b.lastIndexOf('.'); return i <= 0 ? '' : b.slice(i); },
  join: function() { return Array.prototype.slice.call(arguments).join('/').replace(/\/+/g, '/'); },
  join2: function(a, b) { return (String(a) + '/' + String(b)).replace(/\/+/g, '/'); },
  resolve: function() { return Array.prototype.slice.call(arguments).join('/').replace(/\/+/g, '/'); },
};
SIM_PATH_SHIM.posix = SIM_PATH_SHIM;

function makeSimInMemFS(stdout, stderr) {
  var store = {};
  var symlinks = {};
  var dirs = new Set(['/', '/dev', '/workspace', '/workspace/src', '/workspace/out']);
  var fds = {};
  var nextFd = 3;

  function ensureParentDir(path) {
    var parts = String(path).split('/').filter(Boolean);
    var cur = '';
    for (var i = 0; i < parts.length - 1; i++) { cur += '/' + parts[i]; dirs.add(cur); }
  }

  function makeStat(path) {
    path = String(path);
    if (symlinks[path]) {
      return { ino: 3, mode: 0o120777, size: symlinks[path].length, dev: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
               blksize: 4096, blocks: 1, atime: new Date(), mtime: new Date(), ctime: new Date(),
               isDirectory: function(){return false;}, isFile: function(){return false;},
               isSymbolicLink: function(){return true;} };
    }
    if (dirs.has(path)) {
      return { ino: 1, mode: 0o40755, size: 0, dev: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
               blksize: 4096, blocks: 0, atime: new Date(), mtime: new Date(), ctime: new Date(),
               isDirectory: function(){return true;}, isFile: function(){return false;},
               isSymbolicLink: function(){return false;} };
    }
    if (store[path]) {
      return { ino: 2, mode: 0o100644, size: store[path].length, dev: 1, nlink: 1, uid: 0, gid: 0, rdev: 0,
               blksize: 4096, blocks: Math.ceil(store[path].length / 512),
               atime: new Date(), mtime: new Date(), ctime: new Date(),
               isDirectory: function(){return false;}, isFile: function(){return true;},
               isSymbolicLink: function(){return false;} };
    }
    var e = new Error('ENOENT: no such file or directory, stat \'' + path + '\'');
    e.code = 'ENOENT'; throw e;
  }

  var nodeApi = {
    readFileSync: function(path, opts) {
      path = String(path);
      if (!store[path]) { var e = new Error('ENOENT: ' + path); e.code = 'ENOENT'; throw e; }
      var enc = (typeof opts === 'string') ? opts : (opts && opts.encoding);
      return enc ? new TextDecoder().decode(store[path]) : store[path];
    },
    existsSync: function(p) { return dirs.has(p) || !!store[p] || !!symlinks[p]; },
    statSync: makeStat,
    lstatSync: makeStat,
    realpathSync: function(p) {
      var path = String(p);
      return symlinks[path] || path;
    },
    readlinkSync: function(p) {
      var path = String(p);
      if (symlinks[path]) return symlinks[path];
      var e = new Error('EINVAL: invalid argument, readlink \'' + path + '\'');
      e.code = 'EINVAL';
      throw e;
    },
    symlinkSync: function(target, path) {
      var link = String(path);
      ensureParentDir(link);
      symlinks[link] = String(target);
    },
    fstatSync: function(fd) {
      var f = fds[fd]; if (!f) { var e = new Error('EBADF'); e.code = 'EBADF'; throw e; }
      return makeStat(f.path);
    },
    readdirSync: function(path) {
      if (!dirs.has(path)) { var e = new Error('ENOENT: ' + path); e.code = 'ENOENT'; throw e; }
      var prefix = path === '/' ? '/' : path + '/';
      var entries = new Set();
      dirs.forEach(function(d) {
        if (d !== path && d.startsWith(prefix)) {
          var rel = d.slice(prefix.length);
          if (rel.indexOf('/') < 0) entries.add(rel);
        }
      });
      Object.keys(store).forEach(function(f) {
        if (f.startsWith(prefix)) {
          var rel = f.slice(prefix.length);
          if (rel.indexOf('/') < 0) entries.add(rel);
        }
      });
      return Array.from(entries);
    },
    mkdirSync: function(p) { dirs.add(String(p)); },
    rmdirSync: function(p) { dirs.delete(p); },
    unlinkSync: function(p) { delete store[p]; delete symlinks[p]; },
    renameSync: function(from, to) {
      if (store[from]) { store[to] = store[from]; delete store[from]; }
      if (symlinks[from]) { symlinks[to] = symlinks[from]; delete symlinks[from]; }
    },
    chmodSync: function() {}, chownSync: function() {}, utimesSync: function() {}, fsyncSync: function() {},
    ftruncateSync: function(fd, len) {
      var f = fds[fd]; var d = store[f.path] || new Uint8Array(0);
      store[f.path] = len <= d.length ? d.subarray(0, len) : (function(){ var g = new Uint8Array(len); g.set(d); return g; })();
    },
    openSync: function(path, flags) {
      path = String(path);
      var writable;
      if (typeof flags === 'string') {
        writable = flags.indexOf('w') >= 0 || flags.indexOf('a') >= 0 || flags.indexOf('+') >= 0;
      } else {
        var numericFlags = Number(flags) || 0;
        var accessMode = numericFlags & 3; // O_RDONLY=0, O_WRONLY=1, O_RDWR=2
        writable = accessMode !== 0 || !!(numericFlags & 64) || !!(numericFlags & 512) || !!(numericFlags & 1024);
      }
      if (writable) { store[path] = new Uint8Array(0); ensureParentDir(path); }
      else if (!store[path] && !dirs.has(path)) { var e = new Error('ENOENT: ' + path); e.code = 'ENOENT'; throw e; }
      var fd = nextFd++; fds[fd] = { path: path, pos: 0 }; return fd;
    },
    closeSync: function(fd) { delete fds[fd]; },
    readSync: function(fd, buf, bufOffset, length, position) {
      if (fd === 0) return 0;
      var f = fds[fd]; var data = store[f.path] || new Uint8Array(0);
      var pos = position != null ? position : f.pos;
      var avail = Math.min(length, data.length - pos);
      if (avail <= 0) return 0;
      buf.set(data.subarray(pos, pos + avail), bufOffset);
      if (position == null) f.pos += avail;
      return avail;
    },
    writeSync: function(fd, buf, bufOffset, length, position) {
      var src;
      if (typeof buf === 'string') {
        src = new TextEncoder().encode(buf);
      } else if (ArrayBuffer.isView(buf)) {
        src = new Uint8Array(buf.buffer, buf.byteOffset, buf.byteLength);
      } else if (buf instanceof ArrayBuffer) {
        src = new Uint8Array(buf);
      } else {
        src = new Uint8Array(0);
      }
      var start = Number.isFinite(bufOffset) ? Number(bufOffset) : 0;
      if (start < 0) start = 0;
      var writeLen = Number.isFinite(length) ? Number(length) : (src.length - start);
      if (writeLen < 0) writeLen = 0;
      var end = Math.min(src.length, start + writeLen);
      var chunk = src.subarray(start, end);
      if (fd === 1) { stdout.push(new TextDecoder().decode(chunk)); return chunk.length; }
      if (fd === 2) { stderr.push(new TextDecoder().decode(chunk)); return chunk.length; }
      var f = fds[fd]; var pos = position != null ? position : f.pos;
      var data = store[f.path] || new Uint8Array(0);
      var needed = pos + chunk.length;
      if (needed > data.length) { var g = new Uint8Array(needed); g.set(data); data = g; }
      data.set(chunk, pos); store[f.path] = data;
      if (position == null) f.pos += chunk.length;
      return chunk.length;
    },
  };

  return {
    nodeApi: nodeApi,
    // Write a text file before the module loads (used to pre-populate MLIR).
    writeTextFile: function(path, text) {
      var bytes = new TextEncoder().encode(text);
      ensureParentDir(path);
      store[path] = bytes;
    },
  };
}

self.onmessage = async function(event) {
  var req = event.data || {};
  var simJsUrl   = req.simJsUrl;
  var simWasmUrl = req.simWasmUrl;
  var pyodideUrl = req.pyodideUrl;
  var mlir       = req.mlir;
  var topModule  = req.topModule;
  var pyCode     = req.pyCode;
  var shimCode   = req.shimCode;
  var maxTimeNs  = req.maxTimeNs || 1000000;

  var simStdout = [];
  var simStderr = [];
  var logs = [];
  function onLog(msg) {
    var line = String(msg);
    logs.push(line);
    self.postMessage({ type: 'log', line: line });
  }

  try {
    // ── 1. Load the VPI circt-sim WASM ───────────────────────────────────────
    // Fetch the JS source first so we can detect NODERAWFS=1 (recognisable by
    // the unconditional require('path') / require('fs') calls at module level).
    onLog('[cocotb] Loading simulator...');
    var simScript = null;
    try {
      var r = await fetch(simJsUrl);
      if (r.ok) simScript = await r.text();
    } catch(_) {}

    var isNoderawfs = !!simScript && (
      simScript.indexOf('NODERAWFS is currently only supported') >= 0 ||
      simScript.indexOf('var nodePath=require(') >= 0
    );

    var simInMemFS = null;
    var simReady = false;
    self.Module = {
      noInitialRun: true,
      onRuntimeInitialized: function() { simReady = true; },
      print:    function(line) { onLog('[sim] ' + line); },
      printErr: function(line) { onLog('[sim] ' + line); },
      locateFile: function(path) { return path.endsWith('.wasm') ? simWasmUrl : path; },
      instantiateWasm: function(imports, callback) {
        WebAssembly.instantiateStreaming(fetch(simWasmUrl), imports)
          .then(function(r) { callback(r.instance, r.module); })
          .catch(function() {
            fetch(simWasmUrl)
              .then(function(r) { return r.arrayBuffer(); })
              .then(function(buf) { return WebAssembly.instantiate(buf, imports); })
              .then(function(r) { callback(r.instance, r.module); });
          });
        return {};
      }
    };

    if (isNoderawfs && simScript) {
      simInMemFS = makeSimInMemFS(simStdout, simStderr);
      if (typeof self.__dirname === 'undefined') self.__dirname = '/';
      if (typeof self.__filename === 'undefined') self.__filename = '/tool.js';
      var proc = (typeof self.process === 'undefined' || self.process === null) ? {} : self.process;
      if (!proc.versions || typeof proc.versions !== 'object') proc.versions = {};
      if (!proc.versions.node) proc.versions.node = '18.0.0';
      if (typeof proc.version !== 'string') proc.version = 'v18.0.0';
      if (typeof proc.platform !== 'string') proc.platform = 'linux';
      if (!Array.isArray(proc.argv)) proc.argv = ['node', '/tool'];
      if (!proc.type) proc.type = 'worker';
      if (typeof proc.exitCode !== 'number') proc.exitCode = 0;
      if (typeof proc.exit !== 'function') {
        proc.exit = function(code) {
          throw { name: 'ExitStatus', message: 'exit(' + (code | 0) + ')', status: (code | 0) };
        };
      }
      if (typeof proc.on !== 'function') proc.on = function() { return proc; };
      if (!proc.stdout || typeof proc.stdout !== 'object') proc.stdout = {};
      if (!proc.stderr || typeof proc.stderr !== 'object') proc.stderr = {};
      proc.stdout.write = function(s) { simStdout.push(String(s)); };
      proc.stdout.isTTY = false;
      proc.stderr.write = function(s) { simStderr.push(String(s)); };
      proc.stderr.isTTY = false;
      proc.stdin = proc.stdin || null;
      if (!proc.env || typeof proc.env !== 'object') proc.env = {};
      if (typeof proc.cwd !== 'function') proc.cwd = function() { return '/workspace'; };
      proc.binding = function(name) {
        if (name === 'constants') {
          return {
            fs: {
              O_APPEND: 1024,
              O_CREAT: 64,
              O_EXCL: 128,
              O_NOCTTY: 256,
              O_RDONLY: 0,
              O_RDWR: 2,
              O_SYNC: 4096,
              O_TRUNC: 512,
              O_WRONLY: 1,
              O_NOFOLLOW: 131072
            }
          };
        }
        throw new Error('process.binding(' + String(name) + ') is not available');
      };
      self.process = proc;
      if (typeof self.global === 'undefined') self.global = self;
      self.require = function(mod) {
        if (mod === 'path') return SIM_PATH_SHIM;
        if (mod === 'fs') return simInMemFS.nodeApi;
        if (mod === 'crypto') return { randomBytes: function(n) { return crypto.getRandomValues(new Uint8Array(n)); } };
        if (mod === 'child_process') return { spawnSync: function() { return { status: 1, stdout: '', stderr: '' }; } };
        throw new Error('require(\'' + mod + '\') is not available in browser worker');
      };
      (0, eval)(simScript);
    } else {
      if (typeof self.require === 'undefined') {
        self.require = function(mod) {
          if (mod === 'path') return SIM_PATH_SHIM;
          throw new Error('require(\'' + mod + '\') is not available in browser worker');
        };
      }
      importScripts(simJsUrl);
    }

    // Wait for the runtime to initialize and VPI exports to be ready.
    var simModule = await new Promise(function(resolve, reject) {
      var start = Date.now();
      function tick() {
        try {
          var m = self.Module;
          if (m && typeof m.callMain !== 'function' && typeof self.callMain === 'function') {
            m.callMain = self.callMain;
          }
          if (simReady && m && typeof m.callMain === 'function') {
            resolve(m); return;
          }
          if (Date.now() - start >= 45000) {
            reject(new Error('VPI sim module did not become ready in time'));
            return;
          }
          setTimeout(tick, 25);
        } catch(e) { reject(e); }
      }
      tick();
    });

    // ── 1b. Patch Module to expose Emscripten internals needed by VPI helpers ─
    // circt-sim-vpi.js assigns _malloc/_free to module-level globals but not to
    // Module["_malloc"] / Module["_free"].  setValue/getValue and HEAPU8 are
    // absent from EXPORTED_RUNTIME_METHODS for this build.  After importScripts
    // (or indirect eval) these become worker-scope globals we can forward.
    if (typeof simModule._malloc !== 'function') {
      simModule._malloc = function(size) { return _malloc(size); };
    }
    if (typeof simModule._free !== 'function') {
      simModule._free = function(ptr) { _free(ptr); };
    }
    if (typeof simModule.getValue !== 'function') {
      simModule.getValue = function(ptr, type) {
        if (type === 'i32')    return HEAP32[ptr >>> 2];
        if (type === 'double') return HEAPF64[ptr >>> 3];
        return 0;
      };
    }
    if (typeof simModule.setValue !== 'function') {
      simModule.setValue = function(ptr, value, type) {
        if (type === 'i32')    { HEAP32[ptr >>> 2] = value | 0; }
        else if (type === 'double') { HEAPF64[ptr >>> 3] = +value; }
      };
    }
    if (!simModule.HEAPU8) {
      Object.defineProperty(simModule, 'HEAPU8', {
        get: function() { return HEAPU8; },
        configurable: true
      });
    }
    if (!simModule.FS && typeof FS !== 'undefined') {
      simModule.FS = FS;
    }

    // ── 2. Write MLIR to the virtual FS ──────────────────────────────────────
    var mlirPath = '/workspace/out/design.llhd.mlir';
    if (simInMemFS) {
      // NODERAWFS mode: pre-populate the store so callMain can read the file.
      simInMemFS.writeTextFile(mlirPath, mlir);
    } else if (simModule.FS && typeof simModule.FS.writeFile === 'function') {
      try { simModule.FS.mkdir('/workspace'); } catch(_) {}
      try { simModule.FS.mkdir('/workspace/out'); } catch(_) {}
      simModule.FS.writeFile(mlirPath, mlir, { encoding: 'utf8' });
    }

    // ── 3. Load Pyodide ───────────────────────────────────────────────────────
    onLog('[cocotb] Loading Pyodide...');
    importScripts(pyodideUrl);
    var pyodide = await loadPyodide({ stdout: onLog, stderr: onLog });
    onLog('[cocotb] Pyodide ready');

    // ── 4. Install JS→Python bridge on the worker global scope ───────────────
    var _pendingRegistrations = [];
    var _triggerSpecs = {};   // id -> spec, kept for edge-direction filtering
    var _testsDone = false;
    var _testsOk   = false;

    self._cocotb_register_trigger = function(jsonStr) {
      var spec = JSON.parse(jsonStr);
      _pendingRegistrations.push(spec);
      _triggerSpecs[spec.id] = spec;
    };
    self._cocotb_get_signal = function(name) {
      return wsVpiGetSignalValue(simModule, String(name));
    };
    self._cocotb_set_signal = function(name, val) {
      wsVpiSetSignalValue(simModule, String(name), Number(val));
    };
    self._cocotb_log = function(msg) { onLog(String(msg)); };
    // Python passes allPassed as a boolean; Pyodide converts it to JS boolean.
    self._cocotb_tests_done = function(allPassed) { _testsDone = true; _testsOk = !!allPassed; };

    // ── 5. Install the cocotb shim into Pyodide ───────────────────────────────
    pyodide.runPython(shimCode);
    pyodide.runPython("import sys; sys.modules['cocotb'] = sys.modules[__name__]");

    // ── 6. Run the user's Python test file ───────────────────────────────────
    try {
      pyodide.runPython(pyCode);
    } catch(e) {
      onLog('[cocotb] Python error in test file: ' + String(e));
      self.postMessage({ ok: false, logs: logs });
      return;
    }

    // ── 7. Create a no-op cb_rtn function pointer for VPI callbacks ──────────
    // VPIRuntime::registerCb rejects null cb_rtn (returns 0 without storing).
    // We need a valid WASM (i32)->i32 function pointer for the cb_rtn field.
    // Compile a tiny WASM module and insert its export into circt-sim's table.
    // Fallback to WebAssembly.Function (Chrome 97+) or placeholder value 1.
    var noopCbPtr = 0;
    function addFunctionToTable(wasmBytes) {
      try {
        var mod = new WebAssembly.Module(wasmBytes);
        var inst = new WebAssembly.Instance(mod);
        var tbl = (typeof wasmTable !== 'undefined') ? wasmTable : null;
        if (!tbl) return 0;
        // Scan the tail of the table for a null (empty) slot; avoid grow()
        // since Emscripten may compile with a fixed table maximum.
        var slot = -1;
        var len = tbl.length;
        for (var i = Math.max(1, len - 512); i < len; i++) {
          if (tbl.get(i) === null) { slot = i; break; }
        }
        if (slot < 0) {
          // Full scan as last resort.
          for (var j = 1; j < len && slot < 0; j++) {
            if (tbl.get(j) === null) slot = j;
          }
        }
        if (slot < 0) {
          // Table is completely full — try growing.
          try { slot = tbl.length; tbl.grow(1); } catch(_g) { return 0; }
        }
        tbl.set(slot, inst.exports.f);
        return slot;
      } catch(e) { return 0; }
    }
    // WASM: (i32) -> (i32), returns 0
    noopCbPtr = addFunctionToTable(new Uint8Array([
      0x00,0x61,0x73,0x6d, 0x01,0x00,0x00,0x00, // magic + version
      0x01,0x06,0x01,0x60,0x01,0x7f,0x01,0x7f,  // type section: (i32) -> (i32)
      0x03,0x02,0x01,0x00,                       // function section: func 0 : type 0
      0x07,0x05,0x01,0x01,0x66,0x00,0x00,        // export "f" = func 0
      0x0a,0x06,0x01,0x04,0x00,0x41,0x00,0x0b   // code section: i32.const 0, end
    ]));
    if (!noopCbPtr) { try {
      var cFn = new WebAssembly.Function({parameters:['i32'], results:['i32']}, function(){return 0;});
      var tbl = wasmTable; var s = tbl.length; tbl.grow(1); tbl.set(s, cFn); noopCbPtr = s;
    } catch(_) {} }
    // Last resort: value 1 — registerCb only checks non-zero; the patched
    // _circt_vpi_wasm_yield wraps the table call in try-catch.
    var cbRtn = noopCbPtr || 1;

    // ── 8. Install a VPI startup routine in the WASM function table ──────────
    // VPIRuntime::active starts false and is set to true inside callMain.
    // Calling _vpi_register_cb before callMain always returns 0 (no-op).
    //
    // Fix: compile a tiny WASM module (type ()->()) that imports one JS function
    // "r" and calls it. Insert the export into a null slot in the WASM table,
    // then call _vpi_startup_register(slot). circt-sim invokes startup routines
    // via invoke_v(slot) inside callMain once active=true, so "r" runs and can
    // call _vpi_register_cb successfully to register cbStartOfSimulation.
    //
    // Non-zero slot avoids null-pointer guards in VPIRuntime::runStartupRoutines.
    // WASM module is <60 bytes — synchronous compile is allowed in web workers.
    var _vpiStartupSlot = 0;
    (function() {
      try {
        var _tbl = (typeof wasmTable !== 'undefined') ? wasmTable : null;
        if (!_tbl) { onLog('[cocotb] Warning: wasmTable not available'); return; }
        // Scan for a null slot (non-zero) — start from tail to find unused slots.
        var _slot = -1;
        var _len = _tbl.length;
        for (var _i = Math.max(1, _len - 512); _i < _len && _slot < 0; _i++) {
          if (_tbl.get(_i) === null) _slot = _i;
        }
        if (_slot < 0) {
          for (var _j = 1; _j < _len && _slot < 0; _j++) {
            if (_tbl.get(_j) === null) _slot = _j;
          }
        }
        if (_slot < 0) { onLog('[cocotb] Warning: no null slot in wasmTable for VPI startup'); return; }

        // WAT:
        //   (type (func))
        //   (import "env" "r" (func $r))
        //   (func $f (export "f") (call $r))
        var _startupBytes = new Uint8Array([
          0x00,0x61,0x73,0x6d, 0x01,0x00,0x00,0x00,  // magic + version
          0x01,0x04, 0x01,0x60,0x00,0x00,             // type: ()->()
          0x02,0x09, 0x01, 0x03,0x65,0x6e,0x76, 0x01,0x72, 0x00,0x00, // import "env"."r"
          0x03,0x02, 0x01,0x00,                        // func section: func1 type0
          0x07,0x05, 0x01, 0x01,0x66, 0x00,0x01,      // export "f" = func1
          0x0a,0x06, 0x01,0x04, 0x00,0x10,0x00,0x0b   // code: call r(), end
        ]);
        var _startupMod = new WebAssembly.Module(_startupBytes);
        var _startupInst = new WebAssembly.Instance(_startupMod, {
          env: {
            r: function() {
              // Called inside callMain with VPIRuntime::active=true.
              // Errors must not propagate back into invoke_v (would rethrow).
              try {
                var _ptr = simModule._malloc(28);
                simModule.setValue(_ptr +  0, VPI.cbStartOfSimulation, 'i32');
                simModule.setValue(_ptr +  4, cbRtn,                   'i32');
                simModule.setValue(_ptr +  8, 0, 'i32');
                simModule.setValue(_ptr + 12, 0, 'i32');
                simModule.setValue(_ptr + 16, 0, 'i32');
                simModule.setValue(_ptr + 20, 0, 'i32');
                simModule.setValue(_ptr + 24, 0, 'i32');
                var _h = (simModule._vpi_register_cb(_ptr)) | 0;
                simModule._free(_ptr);
                onLog('[cocotb] startup: _vpi_register_cb(cbStartOfSimulation) handle=' + _h);
              } catch(_e) { /* swallow */ }
            }
          }
        });
        _tbl.set(_slot, _startupInst.exports.f);
        _vpiStartupSlot = _slot;
        onLog('[cocotb] VPI startup function installed at table[' + _slot + ']');
      } catch(e) {
        onLog('[cocotb] Warning: VPI startup install failed: ' + e);
      }
    })();

    if (typeof simModule._vpi_startup_register === 'function') {
      if (_vpiStartupSlot) {
        // Happy path: startup function runs inside callMain with active=true.
        simModule._vpi_startup_register(_vpiStartupSlot);
      } else {
        // Fallback: enable VPI subsystem with null marker, then try direct
        // registration (will return 0 if active=false, but worth attempting).
        simModule._vpi_startup_register(0);
        var _startCbData = wsMakeCbData(simModule, VPI.cbStartOfSimulation, cbRtn, 0, 0, 0);
        var _cbHandle = (simModule._vpi_register_cb(_startCbData)) | 0;
        simModule._free(_startCbData);
        if (_cbHandle) {
          onLog('[cocotb] Registered cbStartOfSimulation (direct), handle=' + _cbHandle);
        } else {
          onLog('[cocotb] Warning: _vpi_register_cb returned 0 — VPI callbacks will not fire');
        }
      }
    }

    // ── 9. Set up the Asyncify yield hook ─────────────────────────────────────
    // _circt_vpi_wasm_yield (in circt-sim-vpi.js) calls:
    //   await globalThis.circtSimVpiYieldHook(cbFuncPtr, cbDataPtr)
    //   try { wasmTable.get(cbFuncPtr)(cbDataPtr) } catch(e) {}  [patched]
    // Our hook handles all Python dispatch; cbRtn=1 satisfies registerCb's
    // non-null cb_rtn check; the table[1] call is caught by the try-catch patch.
    self.circtSimVpiYieldHook = async function(cbFuncPtr, cbDataPtr) {
      var reason    = simModule.getValue(cbDataPtr +  0, 'i32');
      var triggerId = simModule.getValue(cbDataPtr + 24, 'i32');

      if (reason === VPI.cbStartOfSimulation) {
        pyodide.runPython('_start_tests_sync()');
        for (var i = 0; i < 50; i++) {
          await pyodide.runPythonAsync('await __import__("asyncio").sleep(0)');
          if (_pendingRegistrations.length > 0 || _testsDone) break;
        }
      } else if (reason !== VPI.cbEndOfSimulation) {
        // A value-change or delay trigger fired.
        // For edge triggers, filter by direction before waking Python.
        // cbValueChange fires on every transition; RisingEdge/FallingEdge must
        // only wake when the actual edge direction matches.
        var spec = _triggerSpecs[triggerId];
        var edgeMismatch = false;
        if (spec && (spec.type === 'rising_edge' || spec.type === 'falling_edge')) {
          var currentVal = wsVpiGetSignalValue(simModule, spec.signal);
          edgeMismatch = (spec.type === 'rising_edge')  ? (currentVal === 0)
                       : (spec.type === 'falling_edge') ? (currentVal !== 0)
                       : false;
        }
        if (edgeMismatch) {
          // Wrong edge — re-register the same trigger and skip waking Python.
          _pendingRegistrations.push(spec);
        } else {
          delete _triggerSpecs[triggerId];
          pyodide.runPython('_vpi_event(' + triggerId + ')');
          for (var i = 0; i < 20; i++) {
            await pyodide.runPythonAsync('await __import__("asyncio").sleep(0)');
            if (_pendingRegistrations.length > 0 || _testsDone) break;
          }
        }
      }

      if (_testsDone) {
        simModule._vpi_control(VPI.vpiFinish, 0);
        return;
      }

      // Register any new VPI callbacks queued by Python.
      var regs = _pendingRegistrations;
      _pendingRegistrations = [];
      for (var j = 0; j < regs.length; j++) {
        wsRegisterVpiTrigger(simModule, regs[j], cbRtn);
      }
    };

    // ── 10. cbStartOfSimulation registered by startup function ───────────────
    // The JS function installed at table[0] (step 8) calls _vpi_register_cb
    // from within callMain when VPIRuntime::active=true. Calling here (before
    // callMain) always fails because active=false at this point.

    // ── 11. Run the simulation ────────────────────────────────────────────────
    // callMain is synchronous. If Asyncify is enabled, the first VPI yield
    // causes WASM to unwind back to callMain (which returns EXITSTATUS).
    // We then await Asyncify.whenDone() to wait for the full simulation cycle
    // (all subsequent yields are handled by wakeUp → doRewind inside the
    // Asyncify machinery until the simulation completes and currData == null).
    var maxTimePs = maxTimeNs * 1000;
    var simArgs = [
      '--resource-guard=false',
      '--mode', 'interpret',
      '--max-time=' + maxTimePs,
      '--top', topModule,
      mlirPath
    ];
    onLog('[cocotb] Starting simulation...');
    try {
      simModule.callMain(simArgs);
    } catch(e) {
      if (!isExitException(e)) {
        onLog('[cocotb] Simulation error: ' + String(e && e.message || e));
      }
    }
    // If Asyncify triggered (currData is non-null after callMain), wait for the
    // full async simulation to complete before proceeding with cleanup.
    if (typeof Asyncify !== 'undefined' && Asyncify.currData) {
      try {
        await Asyncify.whenDone();
      } catch(e) {
        if (!isExitException(e)) {
          onLog('[cocotb] Simulation error: ' + String(e && e.message || e));
        }
      }
    }

    // Merge any stdout/stderr that went through the NODERAWFS path.
    var fsOut = simStdout.join('').trim();
    var fsErr = simStderr.join('').trim();
    if (fsOut) {
      fsOut.split(/\r?\n/).forEach(function(line) { onLog('[sim] ' + line); });
    }
    if (fsErr) {
      fsErr.split(/\r?\n/).forEach(function(line) { onLog('[sim] ' + line); });
    }

    onLog('[cocotb] Simulation complete');
    self.postMessage({ type: 'result', ok: _testsOk, logs: logs });

  } catch(e) {
    self.postMessage({ type: 'result', ok: false, logs: [...logs, '# cocotb error: ' + String(e && e.message || e)] });
  }
};
`;

let cocotbWorkerBlobUrl = null;

function getCocotbWorkerBlobUrl() {
  if (cocotbWorkerBlobUrl) return cocotbWorkerBlobUrl;
  const blob = new Blob([COCOTB_WORKER_SOURCE], { type: 'text/javascript' });
  cocotbWorkerBlobUrl = URL.createObjectURL(blob);
  return cocotbWorkerBlobUrl;
}

function runCocotbInWorker({
  simJsUrl,
  simWasmUrl,
  pyodideUrl,
  mlir,
  topModule,
  pyCode,
  shimCode,
  maxTimeNs,
  onLogLine = null
}) {
  return new Promise((resolve, reject) => {
    const worker = new Worker(getCocotbWorkerBlobUrl());
    // Generous timeout — Pyodide WASM download can take a while on slow connections.
    let timeout;
    const resetTimeout = () => {
      clearTimeout(timeout);
      timeout = setTimeout(() => {
        worker.terminate();
        reject(new Error('cocotb worker timed out'));
      }, 300_000);
    };
    resetTimeout();

    worker.onmessage = (event) => {
      const payload = event.data || {};
      if (payload.type === 'log') {
        resetTimeout();
        if (typeof onLogLine === 'function') onLogLine(String(payload.line || ''));
        return;
      }
      clearTimeout(timeout);
      worker.terminate();
      resolve(payload.type === 'result' ? payload : payload || { ok: false, logs: [] });
    };

    worker.onerror = (event) => {
      clearTimeout(timeout);
      worker.terminate();
      reject(new Error(String(event?.message || 'cocotb worker crashed')));
    };

    worker.postMessage({ simJsUrl, simWasmUrl, pyodideUrl, mlir, topModule, pyCode, shimCode, maxTimeNs });
  });
}

export class CirctWasmAdapter {
  constructor() {
    this.repo = CIRCT_FORK_REPO;
    this.config = getCirctRuntimeConfig();
    this.ready = false;
  }

  async init() {
    if (this.ready) return;

    const requiredTools = ['verilog', 'sim', 'bmc'];
    const missing = requiredTools.filter((name) => {
      const tool = this.config.toolchain?.[name];
      return !tool?.js || !tool?.wasm;
    });

    if (missing.length) {
      throw new Error(`CIRCT toolchain is incomplete in config: ${missing.join(', ')}`);
    }

    this.ready = true;
  }

  async _invokeTool(
    toolName,
    { args, files = {}, readFiles = [], createDirs = [], uvmManifestUrl = null, onOutput = null }
  ) {
    const tool = this.config.toolchain[toolName];
    if (!tool) throw new Error(`Unknown CIRCT tool: ${toolName}`);

    return runToolInWorker({
      jsUrl: toAbsoluteUrl(tool.js),
      wasmUrl: toAbsoluteUrl(tool.wasm),
      args,
      files,
      readFiles,
      createDirs,
      uvmManifestUrl,
      onOutput
    });
  }

  async selfCheck({ lesson = null } = {}) {
    const logs = [];

    try {
      await this.init();

      logs.push(formatCommand('circt-verilog', ['--help']));
      const verilogHelp = await this._invokeTool('verilog', {
        args: ['--help']
      });
      appendNonZeroExit(logs, 'circt-verilog', verilogHelp.exitCode);

      logs.push(formatCommand('circt-sim', ['--help']));
      const simHelp = await this._invokeTool('sim', {
        args: ['--help']
      });
      appendNonZeroExit(logs, 'circt-sim', simHelp.exitCode);

      const ok = verilogHelp.exitCode === 0 && simHelp.exitCode === 0;
      if (verilogHelp.stderr) logs.push(`[stderr] ${verilogHelp.stderr}`);
      if (simHelp.stderr) logs.push(`[stderr] ${simHelp.stderr}`);

      return { ok, logs };
    } catch (error) {
      return {
        ok: false,
        logs: [...logs, `# self-check failed: ${error.message}`]
      };
    }
  }

  async run({ files, top, simulate = true, onStatus = null, onLog = null }) {
    try {
      await this.init();

      const svPaths = sourcePathsFromWorkspace(files);
      if (!svPaths.length) {
        if (typeof onStatus === 'function') onStatus('done');
        return {
          ok: false,
          logs: ['# no SystemVerilog source files found in workspace'],
          waveform: null
        };
      }

      const compileRoots = compileRootSourcePaths(files);
      const topModules = pickTopModules(files, top);
      const normalizedSvPaths = compileRoots.map((path) => normalizePath(path));
      const mlirPath = '/workspace/out/design.llhd.mlir';
      const wavePath = '/workspace/out/waves.vcd';
      const useFullUvm = needsUvmLibrary(files);
      const workspaceFiles = files;
      const uvmManifestUrl = useFullUvm ? getUvmManifestUrl() : null;

      const compileArgs = useFullUvm
        ? removeFlag(this.config.verilogArgs, '--single-unit')
        : [...this.config.verilogArgs];
      if (useFullUvm) {
        compileArgs.push('--uvm-path', UVM_FS_ROOT, '-I', UVM_INCLUDE_ROOT);
      }
      for (const topName of topModules) {
        compileArgs.push('--top', topName);
      }
      compileArgs.push('-o', mlirPath, ...normalizedSvPaths);

      const logs = [];
      const emitLog = (entry) => {
        logs.push(entry);
        if (typeof onLog === 'function') onLog(entry);
      };
      const makeToolOutputHandler = () => {
        let sawStream = false;
        return {
          onOutput: ({ stream, line }) => {
            sawStream = true;
            emitLog(`[${stream}] ${line}`);
          },
          sawStream: () => sawStream
        };
      };

      emitLog(formatCommand('circt-verilog', compileArgs));

      if (typeof onStatus === 'function') onStatus('compiling');
      let compile;
      const compileStream = makeToolOutputHandler();
      try {
        compile = await this._invokeTool('verilog', {
          args: compileArgs,
          files: Object.fromEntries(
            Object.entries(workspaceFiles).map(([path, content]) => [normalizePath(path), content])
          ),
          readFiles: [mlirPath],
          createDirs: ['/workspace/out'],
          uvmManifestUrl,
          onOutput: compileStream.onOutput
        });
      } catch (error) {
        const text = String(error?.message || error || '');
        if (useFullUvm && text.includes('Aborted(OOM)')) {
          emitLog('# circt-verilog: out of memory compiling UVM — rebuild wasm with larger heap');
          if (typeof onStatus === 'function') onStatus('done');
          return { ok: false, logs, waveform: null };
        }
        throw error;
      }
      if (!compileStream.sawStream()) {
        if (compile.stdout) emitLog(`[stdout] ${compile.stdout}`);
        if (compile.stderr) emitLog(`[stderr] ${compile.stderr}`);
      }
      appendNonZeroExit(logs, 'circt-verilog', compile.exitCode, emitLog);

      const rawMlir = compile.files?.[mlirPath] || null;
      // Add name attributes to llhd.sig ops that lack them so circt-sim's VCD
      // writer can emit $var entries. circt-verilog only sets name on module
      // port connections; testbench-level logic signals get no name attribute.
      // We use the SSA result identifier (%clk → name "clk") as the signal name.
      const loweredMlir = rawMlir
        ? rawMlir.replace(
            /(%([a-zA-Z_]\w*)\s*=\s*llhd\.sig\s+)(?!name\s+")/g,
            (_m, prefix, sigName) => `${prefix}name "${sigName}" `
          )
        : null;
      if (compile.exitCode !== 0 || !loweredMlir) {
        if (!loweredMlir) emitLog('# lowered MLIR output was not produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs, waveform: null };
      }

      // Run simulation by default so lessons without waveform support still
      // execute $display/$finish behavior (e.g. Welcome). Lessons can opt out
      // explicitly via `simulate: false`.
      const shouldSimulate = simulate !== false;
      if (!shouldSimulate) {
        if (typeof onStatus === 'function') onStatus('done');
        return {
          ok: true,
          logs,
          waveform: null
        };
      }

      const simArgs = forceInterpretSimMode([...this.config.simArgs]);
      for (const topName of topModules) {
        simArgs.push('--top', topName);
      }
      // Always request a VCD. UI decides whether to expose Waves based on
      // whether a valid VCD with signal definitions was actually produced.
      simArgs.push('--vcd', wavePath);
      // Trace all signals (default is ports only; @tb has no ports).
      simArgs.push('--trace-all');
      simArgs.push(mlirPath);

      emitLog(formatCommand('circt-sim', simArgs));

      if (typeof onStatus === 'function') onStatus('running');
      const simStream = makeToolOutputHandler();
      const sim = await this._invokeTool('sim', {
        args: simArgs,
        files: {
          [mlirPath]: loweredMlir
        },
        readFiles: [wavePath],
        createDirs: ['/workspace/out'],
        onOutput: simStream.onOutput
      });

      if (!simStream.sawStream()) {
        if (sim.stdout) emitLog(`[stdout] ${sim.stdout}`);
        if (sim.stderr) emitLog(`[stderr] ${sim.stderr}`);
      }
      appendNonZeroExit(logs, 'circt-sim', sim.exitCode, emitLog);

      const rawVcdText = sim.files?.[wavePath] || null;
      const cleanedVcdText = removeInlinedPortsFromVcd(rawVcdText);
      const vcdText = hasVcdSignalDefinitions(cleanedVcdText) ? cleanedVcdText : null;

      if (typeof onStatus === 'function') onStatus('done');
      return {
        ok: compile.exitCode === 0 && sim.exitCode === 0,
        logs,
        waveform: vcdText
          ? {
              path: wavePath,
              text: vcdText
            }
          : null
      };
    } catch (error) {
      if (typeof onStatus === 'function') onStatus('done');
      return {
        ok: false,
        logs: [
          `# runtime unavailable: ${error.message}`,
          `# circt-verilog js: ${this.config.toolchain.verilog.js}`,
          `# circt-verilog wasm: ${this.config.toolchain.verilog.wasm}`,
          `# circt-sim js: ${this.config.toolchain.sim.js}`,
          `# circt-sim wasm: ${this.config.toolchain.sim.wasm}`,
          '# run scripts/setup-circt.sh and npm run sync:circt to refresh artifacts'
        ],
        waveform: null
      };
    }
  }

  async runBmc({ files, top, onStatus = null, onLog = null }) {
    try {
      await this.init();

      // BMC only needs the design — exclude testbench files so the tool
      // doesn't pick 'tb' as the top module and introduce spurious inputs.
      const filteredDesignFiles = Object.fromEntries(
        Object.entries(files).filter(([path]) => !isTestbench(path))
      );
      const userSvPaths = sourcePathsFromWorkspace(filteredDesignFiles);
      if (!userSvPaths.length) {
        if (typeof onStatus === 'function') onStatus('done');
        return {
          ok: false,
          logs: ['# no SystemVerilog source files found in workspace']
        };
      }

      const useFullUvm = needsUvmLibrary(filteredDesignFiles);
      const designFiles = filteredDesignFiles;
      const compileRoots = compileRootSourcePaths(filteredDesignFiles);
      const uvmManifestUrl = useFullUvm ? getUvmManifestUrl() : null;

      // Use the provided top name directly — don't let pickTopModules pick 'tb'.
      const topModule = top || filename(userSvPaths[0]).replace(/\.[^.]+$/, '');
      const mlirPath = '/workspace/out/design.mlir';
      const smtPath = '/workspace/out/check.smt2';

      const compileArgs = [
        ...(useFullUvm
          ? removeFlag(this.config.verilogArgs, '--single-unit')
          : this.config.verilogArgs),
        ...(useFullUvm ? ['--uvm-path', UVM_FS_ROOT, '-I', UVM_INCLUDE_ROOT] : []),
        '--top',
        topModule,
        '-o',
        mlirPath,
        ...compileRoots.map((p) => normalizePath(p)),
      ];

      const logs = [];
      const emitLog = (entry) => {
        logs.push(entry);
        if (typeof onLog === 'function') onLog(entry);
      };
      const makeToolOutputHandler = () => {
        let sawStream = false;
        return {
          onOutput: ({ stream, line }) => {
            sawStream = true;
            emitLog(`[${stream}] ${line}`);
          },
          sawStream: () => sawStream
        };
      };
      emitLog(formatCommand('circt-verilog', compileArgs));

      if (typeof onStatus === 'function') onStatus('compiling');
      let compile;
      const compileStream = makeToolOutputHandler();
      try {
        compile = await this._invokeTool('verilog', {
          args: compileArgs,
          files: Object.fromEntries(
            Object.entries(designFiles).map(([path, content]) => [normalizePath(path), content])
          ),
          readFiles: [mlirPath],
          createDirs: ['/workspace/out'],
          uvmManifestUrl,
          onOutput: compileStream.onOutput
        });
      } catch (error) {
        const text = String(error?.message || error || '');
        if (useFullUvm && text.includes('Aborted(OOM)')) {
          emitLog('# circt-verilog: out of memory compiling UVM — rebuild wasm with larger heap');
          if (typeof onStatus === 'function') onStatus('done');
          return { ok: false, logs };
        }
        throw error;
      }
      if (!compileStream.sawStream()) {
        if (compile.stdout) emitLog(`[stdout] ${compile.stdout}`);
        if (compile.stderr) emitLog(`[stderr] ${compile.stderr}`);
      }
      appendNonZeroExit(logs, 'circt-verilog', compile.exitCode, emitLog);

      const mlirText = compile.files?.[mlirPath] || null;
      if (compile.exitCode !== 0 || !mlirText) {
        if (!mlirText) emitLog('# MLIR output was not produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      // Substitute {top} and {input} placeholders in bmc args.
      // DEFAULT_BMC_ARGS writes SMT-LIB to smtPath; read it back after the run.
      const bmcArgs = this.config.bmcArgs.map((arg) =>
        arg.replace('{top}', topModule).replace('{input}', mlirPath)
      );

      emitLog(formatCommand('circt-bmc', bmcArgs));

      if (typeof onStatus === 'function') onStatus('running');
      const bmcStream = makeToolOutputHandler();
      const bmc = await this._invokeTool('bmc', {
        args: bmcArgs,
        files: { [mlirPath]: mlirText },
        readFiles: [smtPath],
        createDirs: ['/workspace/out'],
        onOutput: bmcStream.onOutput
      });

      if (!bmcStream.sawStream() && bmc.stdout) emitLog(`[stdout] ${bmc.stdout}`);
      // Filter the "z3 not found" line — we handle z3 ourselves below.
      const bmcStderr = (bmc.stderr || '')
        .split('\n')
        .filter((l) => !l.includes('z3 not found') && !l.includes('cannot run SMT-LIB'))
        .join('\n')
        .trim();
      if (!bmcStream.sawStream() && bmcStderr) emitLog(`[stderr] ${bmcStderr}`);
      appendNonZeroExit(logs, 'circt-bmc', bmc.exitCode, emitLog);

      const smtlibText = bmc.files?.[smtPath] || null;
      if (!smtlibText) {
        emitLog('# no SMT-LIB output produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      // ── z3 phase ──────────────────────────────────────────────────────────
      const z3out = await evalSmtlib(smtlibText);

      const z3lines = (z3out || '').trim().split('\n').filter(Boolean);
      for (const line of z3lines) emitLog(`[z3] ${line}`);

      // unsat for every bound → all properties hold up to the bound.
      // Any sat → a counterexample was found.
      const hasSat = z3lines.some((l) => l.trim() === 'sat');
      const allUnsat = z3lines.length > 0 && z3lines.every((l) => l.trim() === 'unsat');

      if (typeof onStatus === 'function') onStatus('done');
      return { ok: allUnsat, logs };

    } catch (error) {
      if (typeof onStatus === 'function') onStatus('done');
      return {
        ok: false,
        logs: [
          `# runtime unavailable: ${error.message}`,
          `# circt-bmc js: ${this.config.toolchain.bmc.js}`,
          `# circt-bmc wasm: ${this.config.toolchain.bmc.wasm}`,
          '# run scripts/setup-circt.sh to refresh artifacts'
        ]
      };
    }
  }

  async runCocotb({ files, top, onStatus = null, onLog = null }) {
    try {
      await this.init();

      // Compile only the SV design files (no testbenches, no .py files).
      const designFiles = Object.fromEntries(
        Object.entries(files).filter(([path]) =>
          !path.endsWith('.py') && !isTestbench(path)
        )
      );

      const svPaths = sourcePathsFromWorkspace(designFiles);
      if (!svPaths.length) {
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs: ['# no SystemVerilog design files found in workspace'] };
      }

      const compileRoots = compileRootSourcePaths(designFiles);
      const topModules = pickTopModules(designFiles, top);
      const topModule = topModules[0];
      const mlirPath = '/workspace/out/design.llhd.mlir';

      // Use 1ps/1ps precision so VPI sim-time units = 1 ps.
      // wsMakeVpiTime in the cocotb worker converts femtoseconds → ps (÷1000),
      // which is exact when the simulator resolution is 1 ps.
      const cocotbVerilogArgs = this.config.verilogArgs.map((arg, i, arr) =>
        arr[i - 1] === '--timescale' ? '1ps/1ps' : arg
      );
      const compileArgs = [
        ...cocotbVerilogArgs,
        '--top', topModule,
        '-o', mlirPath,
        ...compileRoots.map((p) => normalizePath(p))
      ];

      const logs = [];
      const emitLog = (entry) => {
        logs.push(entry);
        if (typeof onLog === 'function') onLog(entry);
      };
      const makeToolOutputHandler = () => {
        let sawStream = false;
        return {
          onOutput: ({ stream, line }) => {
            sawStream = true;
            emitLog(`[${stream}] ${line}`);
          },
          sawStream: () => sawStream
        };
      };
      emitLog(formatCommand('circt-verilog', compileArgs));

      if (typeof onStatus === 'function') onStatus('compiling');
      const compileStream = makeToolOutputHandler();
      const compile = await this._invokeTool('verilog', {
        args: compileArgs,
        files: Object.fromEntries(
          Object.entries(designFiles).map(([path, content]) => [normalizePath(path), content])
        ),
        readFiles: [mlirPath],
        createDirs: ['/workspace/out'],
        onOutput: compileStream.onOutput
      });
      if (!compileStream.sawStream()) {
        if (compile.stdout) emitLog(`[stdout] ${compile.stdout}`);
        if (compile.stderr) emitLog(`[stderr] ${compile.stderr}`);
      }
      appendNonZeroExit(logs, 'circt-verilog', compile.exitCode, emitLog);

      const mlirText = compile.files?.[mlirPath] || null;
      if (compile.exitCode !== 0 || !mlirText) {
        if (!mlirText) emitLog('# MLIR output was not produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      // Find the Python test file(s).
      const pyEntries = Object.entries(files).filter(([path]) => path.endsWith('.py'));
      if (!pyEntries.length) {
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs: [...logs, '# no Python test file found in workspace'] };
      }
      const [, pyCode] = pyEntries[0];

      // Check that the VPI sim is configured.
      const simVpi = this.config.toolchain.simVpi;
      if (!simVpi?.js || !simVpi?.wasm) {
        emitLog('# VPI-capable circt-sim not configured');
        emitLog('# set VITE_CIRCT_SIM_VPI_JS_URL and VITE_CIRCT_SIM_VPI_WASM_URL in .env');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      if (typeof onStatus === 'function') onStatus('running');

      const result = await runCocotbInWorker({
        simJsUrl:   toAbsoluteUrl(simVpi.js),
        simWasmUrl: toAbsoluteUrl(simVpi.wasm),
        pyodideUrl: this.config.pyodideUrl,
        mlir:       mlirText,
        topModule,
        pyCode,
        shimCode:   COCOTB_SHIM,
        maxTimeNs:  1_000_000,
        onLogLine:  emitLog
      });

      if (Array.isArray(result.logs) && result.logs.length) {
        const streamedSet = new Set(logs);
        for (const line of result.logs) {
          if (!streamedSet.has(line)) {
            emitLog(line);
            streamedSet.add(line);
          }
        }
      }

      if (typeof onStatus === 'function') onStatus('done');
      return { ok: result.ok, logs, waveform: null };

    } catch (error) {
      if (typeof onStatus === 'function') onStatus('done');
      return {
        ok: false,
        logs: [
          `# cocotb runtime error: ${error.message}`,
          `# VPI sim js:   ${this.config.toolchain.simVpi?.js}`,
          `# VPI sim wasm: ${this.config.toolchain.simVpi?.wasm}`,
          `# Pyodide URL:  ${this.config.pyodideUrl}`
        ]
      };
    }
  }

  async runLec({ files, module1, module2, onStatus = null, onLog = null }) {
    try {
      await this.init();

      const designFiles = Object.fromEntries(
        Object.entries(files).filter(([path]) => !isTestbench(path))
      );
      const svPaths = sourcePathsFromWorkspace(designFiles);
      if (!svPaths.length) {
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs: ['# no SystemVerilog source files found in workspace'] };
      }

      const compileRoots = compileRootSourcePaths(designFiles);
      const mlirPath = '/workspace/out/design.mlir';
      const smtPath = '/workspace/out/check.smt2';

      // LEC operates on the HW/Comb dialect — use --ir-hw, not --ir-llhd.
      const compileArgs = [
        ...this.config.lecVerilogArgs,
        '-o', mlirPath,
        ...compileRoots.map((p) => normalizePath(p))
      ];

      const logs = [];
      const emitLog = (entry) => {
        logs.push(entry);
        if (typeof onLog === 'function') onLog(entry);
      };
      const makeToolOutputHandler = () => {
        let sawStream = false;
        return {
          onOutput: ({ stream, line }) => {
            sawStream = true;
            emitLog(`[${stream}] ${line}`);
          },
          sawStream: () => sawStream
        };
      };
      emitLog(formatCommand('circt-verilog', compileArgs));

      if (typeof onStatus === 'function') onStatus('compiling');
      const compileStream = makeToolOutputHandler();
      const compile = await this._invokeTool('verilog', {
        args: compileArgs,
        files: Object.fromEntries(
          Object.entries(designFiles).map(([path, content]) => [normalizePath(path), content])
        ),
        readFiles: [mlirPath],
        createDirs: ['/workspace/out'],
        onOutput: compileStream.onOutput
      });
      if (!compileStream.sawStream()) {
        if (compile.stdout) emitLog(`[stdout] ${compile.stdout}`);
        if (compile.stderr) emitLog(`[stderr] ${compile.stderr}`);
      }
      appendNonZeroExit(logs, 'circt-verilog', compile.exitCode, emitLog);

      const mlirText = compile.files?.[mlirPath] || null;
      if (compile.exitCode !== 0 || !mlirText) {
        if (!mlirText) emitLog('# MLIR output was not produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      const lecArgs = this.config.lecArgs.map((arg) =>
        arg.replace('{module1}', module1)
           .replace('{module2}', module2)
           .replace('{input}', mlirPath)
      );

      emitLog(formatCommand('circt-lec', lecArgs));

      if (typeof onStatus === 'function') onStatus('running');
      const lecStream = makeToolOutputHandler();
      const lec = await this._invokeTool('lec', {
        args: lecArgs,
        files: { [mlirPath]: mlirText },
        readFiles: [smtPath],
        createDirs: ['/workspace/out'],
        onOutput: lecStream.onOutput
      });

      if (!lecStream.sawStream() && lec.stdout) emitLog(`[stdout] ${lec.stdout}`);
      const lecStderr = (lec.stderr || '')
        .split('\n')
        .filter((l) => !l.includes('z3 not found') && !l.includes('cannot run SMT-LIB'))
        .join('\n')
        .trim();
      if (!lecStream.sawStream() && lecStderr) emitLog(`[stderr] ${lecStderr}`);
      appendNonZeroExit(logs, 'circt-lec', lec.exitCode, emitLog);

      const smtlibText = lec.files?.[smtPath] || null;
      if (!smtlibText) {
        emitLog('# no SMT-LIB output produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      const z3out = await evalSmtlib(smtlibText);

      const z3lines = (z3out || '').trim().split('\n').filter(Boolean);
      for (const line of z3lines) emitLog(`[z3] ${line}`);

      // unsat → no input makes the circuits differ → equivalent.
      // sat   → a distinguishing input exists → not equivalent.
      const hasSat = z3lines.some((l) => l.trim() === 'sat');
      const allUnsat = z3lines.length > 0 && z3lines.every((l) => l.trim() === 'unsat');

      if (hasSat) {
        // Extract a counterexample using a fresh z3 instance.
        // The browser's Emscripten build sets an internal ABORT flag after the
        // first Z3_eval_smtlib2_string call, so subsequent calls on the same
        // instance throw "Program terminated with exit(1)". A fresh instance
        // has no such state. (~50 ms overhead; WASM is cached by the browser.)
        try {
          const freshEm = await getFreshZ3Module();
          const modelOut = await evalSmtlib(smtlibText + '\n(get-model)\n', { produceModels: true, em: freshEm });
          // Collapse whitespace so multi-line define-fun entries match as one unit.
          const modelFlat = (modelOut || '').replace(/\s+/g, ' ');
          const assignments = [];
          // BitVec: (define-fun |name| () (_ BitVec N) #xVAL)
          const bvRe = /\(define-fun\s+\|?(\S+?)\|?\s+\(\)\s+\(_\s+BitVec\s+\d+\)\s+(#x[0-9a-fA-F]+|#b[01]+)\s*\)/g;
          let m;
          while ((m = bvRe.exec(modelFlat)) !== null) {
            const [, name, val] = m;
            const num = val.startsWith('#x') ? parseInt(val.slice(2), 16) : parseInt(val.slice(2), 2);
            assignments.push(`${name}=${num}`);
          }
          // Bool: (define-fun |name| () Bool true/false)
          const boolRe = /\(define-fun\s+\|?(\S+?)\|?\s+\(\)\s+Bool\s+(true|false)\s*\)/g;
          while ((m = boolRe.exec(modelFlat)) !== null) {
            assignments.push(`${m[1]}=${m[2] === 'true' ? 1 : 0}`);
          }
          if (assignments.length > 0) {
            emitLog(`# counterexample: ${assignments.join(' ')}`);
          } else {
            emitLog(`# model: ${modelOut?.trim()}`);
          }
        } catch (err) {
          emitLog(`# model extraction failed: ${err.message}`);
        }
      }

      if (typeof onStatus === 'function') onStatus('done');
      return { ok: allUnsat, logs };

    } catch (error) {
      if (typeof onStatus === 'function') onStatus('done');
      return {
        ok: false,
        logs: [
          `# runtime unavailable: ${error.message}`,
          `# circt-lec js: ${this.config.toolchain.lec?.js}`,
          `# circt-lec wasm: ${this.config.toolchain.lec?.wasm}`,
          '# run scripts/setup-circt.sh to refresh artifacts'
        ]
      };
    }
  }
}

export function createCirctWasmAdapter() {
  return new CirctWasmAdapter();
}
