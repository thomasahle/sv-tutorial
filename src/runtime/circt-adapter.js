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

function appendNonZeroExit(logs, tool, exitCode) {
  if (exitCode !== 0) {
    logs.push(`# ${tool} exit code: ${exitCode}`);
  }
}

function removeFlag(args, flag) {
  return (args || []).filter((arg) => arg !== flag);
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
function makeInMemFS() {
  var store = {};
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
    existsSync: function(p) { return dirs.has(p) || !!store[p] || !!remoteFiles[p] || tryFetchIntoStore(p); },
    statSync: makeStat,
    lstatSync: makeStat,
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
    unlinkSync: function(p) { delete store[p]; },
    renameSync: function(from, to) { store[to] = store[from]; delete store[from]; },
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
      var writable = typeof flags === 'string' ? (flags.indexOf('w') >= 0 || flags.indexOf('a') >= 0) : !!(flags & 1);
      if (writable) { store[path] = new Uint8Array(0); ensureParentDir(path); }
      else if (!store[path] && !dirs.has(path) && !remoteFiles[path] && !tryFetchIntoStore(path)) { var e = new Error('ENOENT: ' + path); e.code = 'ENOENT'; throw e; }
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
      var src = (buf instanceof Uint8Array) ? buf : new Uint8Array(buf.buffer ? buf.buffer : buf);
      var chunk = src.subarray(bufOffset, bufOffset + length);
      if (fd === 1) { stdoutChunks.push(new TextDecoder().decode(chunk)); return length; }
      if (fd === 2) { stderrChunks.push(new TextDecoder().decode(chunk)); return length; }
      var f = fds[fd]; var pos = position != null ? position : f.pos;
      var data = store[f.path] || new Uint8Array(0);
      var needed = pos + length;
      if (needed > data.length) { var g = new Uint8Array(needed); g.set(data); data = g; }
      data.set(chunk, pos); store[f.path] = data;
      if (position == null) f.pos += length;
      return length;
    },
  };

  return {
    nodeApi: nodeApi,
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

  try {
    self.Module = {
      noInitialRun: true,
      onRuntimeInitialized: () => {
        console.log('[circt-worker] onRuntimeInitialized fired');
        circtWorkerRuntimeReady = true;
      },
      print: (line) => stdout.push(String(line)),
      printErr: (line) => stderr.push(String(line)),
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
      inMemFS = makeInMemFS();
      if (typeof self.__dirname === 'undefined') self.__dirname = '/';
      if (typeof self.__filename === 'undefined') self.__filename = '/tool.js';
      if (typeof self.process === 'undefined' || self.process === null) {
        self.process = {
          versions: { node: '18.0.0' },
          argv: ['node', '/tool'],
          type: 'worker',
          exitCode: 0,
          // Emscripten calls process.exit(code) in Node.js mode on completion.
          // Throw an ExitStatus-shaped error so isExitException() catches it.
          exit: function(code) {
            throw { name: 'ExitStatus', message: 'exit(' + (code | 0) + ')', status: (code | 0) };
          },
          on: function() { return self.process; },
          stdout: { write: function(s) { stdout.push(String(s)); }, isTTY: false },
          stderr: { write: function(s) { stderr.push(String(s)); }, isTTY: false },
          stdin: null,
          env: {},
          cwd: function() { return '/workspace'; }
        };
      }
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
          inMemFS.registerRemoteFile(fsPath, sourceUrl);
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
    writeWorkspaceFiles(module.FS, req.files || {});
    for (const dir of req.createDirs || []) {
      ensureDir(module.FS, dir);
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

    // For NODERAWFS builds, stdout/stderr may go through fs.writeSync(1/2) rather
    // than Module.print/printErr. Merge both capture paths.
    if (inMemFS) {
      const fsOut = inMemFS.getStdout().trim();
      const fsErr = inMemFS.getStderr().trim();
      if (fsOut) stdout.push(fsOut);
      if (fsErr) stderr.push(fsErr);
    }

    const files = readWorkspaceFiles(module.FS, req.readFiles || []);
    self.postMessage({
      ok: true,
      exitCode,
      stdout: stdout.join('\n').trim(),
      stderr: stderr.join('\n').trim(),
      files
    });
  } catch (error) {
    self.postMessage({
      ok: false,
      exitCode: 1,
      stdout: stdout.join('\n').trim(),
      stderr: stderr.join('\n').trim(),
      files: {},
      error: String((error && error.message) || error || 'unknown worker failure')
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

function runToolInWorker({ jsUrl, wasmUrl, args, files, readFiles, createDirs = [], uvmManifestUrl = null }) {
  return new Promise((resolve, reject) => {
    const worker = new Worker(getWorkerBlobUrl());
    const timeout = setTimeout(() => {
      worker.terminate();
      reject(new Error(`${jsUrl}: tool invocation timed out`));
    }, 90000);

    worker.onmessage = (event) => {
      clearTimeout(timeout);
      worker.terminate();
      const payload = event.data || {};
      if (!payload.ok) {
        const prefix = payload.error || 'tool invocation failed';
        const stderr = payload.stderr ? ` :: ${payload.stderr}` : '';
        reject(new Error(`${prefix}${stderr}`));
        return;
      }
      resolve(payload);
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
 * Evaluate an SMT-LIB 2 string with z3 and return the output string.
 * Uses the synchronous Z3_eval_smtlib2_string C API via Emscripten ccall.
 */
async function evalSmtlib(smtlibText) {
  const em = await getZ3Module();
  const cfg = em.ccall('Z3_mk_config', 'number', [], []);
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
    existsSync: function(p) { return dirs.has(p) || !!store[p]; },
    statSync: makeStat,
    lstatSync: makeStat,
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
    unlinkSync: function(p) { delete store[p]; },
    renameSync: function(from, to) { store[to] = store[from]; delete store[from]; },
    chmodSync: function() {}, chownSync: function() {}, utimesSync: function() {}, fsyncSync: function() {},
    ftruncateSync: function(fd, len) {
      var f = fds[fd]; var d = store[f.path] || new Uint8Array(0);
      store[f.path] = len <= d.length ? d.subarray(0, len) : (function(){ var g = new Uint8Array(len); g.set(d); return g; })();
    },
    openSync: function(path, flags) {
      path = String(path);
      var writable = typeof flags === 'string' ? (flags.indexOf('w') >= 0 || flags.indexOf('a') >= 0) : !!(flags & 1);
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
      var src = (buf instanceof Uint8Array) ? buf : new Uint8Array(buf.buffer ? buf.buffer : buf);
      var chunk = src.subarray(bufOffset, bufOffset + length);
      if (fd === 1) { stdout.push(new TextDecoder().decode(chunk)); return length; }
      if (fd === 2) { stderr.push(new TextDecoder().decode(chunk)); return length; }
      var f = fds[fd]; var pos = position != null ? position : f.pos;
      var data = store[f.path] || new Uint8Array(0);
      var needed = pos + length;
      if (needed > data.length) { var g = new Uint8Array(needed); g.set(data); data = g; }
      data.set(chunk, pos); store[f.path] = data;
      if (position == null) f.pos += length;
      return length;
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
  function onLog(msg) { logs.push(String(msg)); }

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
      if (typeof self.process === 'undefined' || self.process === null) {
        self.process = {
          versions: { node: '18.0.0' },
          argv: ['node', '/tool'],
          type: 'worker',
          exitCode: 0,
          exit: function(code) {
            throw { name: 'ExitStatus', message: 'exit(' + (code | 0) + ')', status: (code | 0) };
          },
          on: function() { return self.process; },
          stdout: { write: function(s) { simStdout.push(String(s)); }, isTTY: false },
          stderr: { write: function(s) { simStderr.push(String(s)); }, isTTY: false },
          stdin: null,
          env: {},
          cwd: function() { return '/workspace'; }
        };
      }
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

    // ── 7. Enable VPI for this run ────────────────────────────────────────────
    // Pass 0 as the startup routine — acts as a "just enable VPI" marker so
    // hasRegisteredVPIStartupRoutines() returns true without needing addFunction.
    if (typeof simModule._vpi_startup_register === 'function') {
      simModule._vpi_startup_register(0);
    }

    // ── 8. Set up the Asyncify yield hook ─────────────────────────────────────
    // circt-sim-vpi-wasm.js calls:
    //   await globalThis.circtSimVpiYieldHook(cbFuncPtr, cbDataPtr)
    //   if (cbFuncPtr) wasmTable.get(cbFuncPtr)(cbDataPtr)
    // All VPI callbacks use cbRtn=0, so only the hook does meaningful work.
    // The hook reads reason and user_data directly from the cbDataPtr struct.
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

      // Register any new VPI callbacks queued by Python (cbRtn=0 throughout).
      var regs = _pendingRegistrations;
      _pendingRegistrations = [];
      for (var j = 0; j < regs.length; j++) {
        wsRegisterVpiTrigger(simModule, regs[j], 0);
      }
    };

    // ── 9. Register cbStartOfSimulation ──────────────────────────────────────
    // cbRtn=0: yield hook handles all dispatch; wasmTable.get(0) is skipped.
    var startCbData = wsMakeCbData(simModule, VPI.cbStartOfSimulation, 0, 0, 0, 0);
    simModule._vpi_register_cb(startCbData);
    simModule._free(startCbData);

    // ── 10. Run the simulation (Asyncify — callMain returns a Promise) ────────
    var maxTimePs = maxTimeNs * 1000;
    var simArgs = [
      'circt-sim',
      '--resource-guard=false',
      '--max-time=' + maxTimePs,
      '--top', topModule,
      mlirPath
    ];
    onLog('[cocotb] Starting simulation...');
    try {
      await simModule.callMain(simArgs);
    } catch(e) {
      if (!isExitException(e)) {
        onLog('[cocotb] Simulation error: ' + String(e && e.message || e));
      }
    }

    // Merge any stdout/stderr that went through the NODERAWFS path.
    var fsOut = simStdout.join('').trim();
    var fsErr = simStderr.join('').trim();
    if (fsOut) onLog('[sim] ' + fsOut);
    if (fsErr) onLog('[sim] ' + fsErr);

    onLog('[cocotb] Simulation complete');
    self.postMessage({ ok: _testsOk, logs: logs });

  } catch(e) {
    self.postMessage({ ok: false, logs: [...logs, '# cocotb error: ' + String(e && e.message || e)] });
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

function runCocotbInWorker({ simJsUrl, simWasmUrl, pyodideUrl, mlir, topModule, pyCode, shimCode, maxTimeNs }) {
  return new Promise((resolve, reject) => {
    const worker = new Worker(getCocotbWorkerBlobUrl());
    // Generous timeout — Pyodide WASM download can take a while on slow connections.
    const timeout = setTimeout(() => {
      worker.terminate();
      reject(new Error('cocotb worker timed out'));
    }, 300_000);

    worker.onmessage = (event) => {
      clearTimeout(timeout);
      worker.terminate();
      resolve(event.data || { ok: false, logs: [] });
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

  async _invokeTool(toolName, { args, files = {}, readFiles = [], createDirs = [], uvmManifestUrl = null }) {
    const tool = this.config.toolchain[toolName];
    if (!tool) throw new Error(`Unknown CIRCT tool: ${toolName}`);

    return runToolInWorker({
      jsUrl: toAbsoluteUrl(tool.js),
      wasmUrl: toAbsoluteUrl(tool.wasm),
      args,
      files,
      readFiles,
      createDirs,
      uvmManifestUrl
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

  async run({ files, top, simulate = true, onStatus = null }) {
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
      logs.push(formatCommand('circt-verilog', compileArgs));

      if (typeof onStatus === 'function') onStatus('compiling');
      let compile;
      try {
        compile = await this._invokeTool('verilog', {
          args: compileArgs,
          files: Object.fromEntries(
            Object.entries(workspaceFiles).map(([path, content]) => [normalizePath(path), content])
          ),
          readFiles: [mlirPath],
          createDirs: ['/workspace/out'],
          uvmManifestUrl
        });
      } catch (error) {
        const text = String(error?.message || error || '');
        if (useFullUvm && text.includes('Aborted(OOM)')) {
          logs.push('# circt-verilog: out of memory compiling UVM — rebuild wasm with larger heap');
          if (typeof onStatus === 'function') onStatus('done');
          return { ok: false, logs, waveform: null };
        }
        throw error;
      }
      if (compile.stdout) logs.push(`[stdout] ${compile.stdout}`);
      if (compile.stderr) logs.push(`[stderr] ${compile.stderr}`);
      appendNonZeroExit(logs, 'circt-verilog', compile.exitCode);

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
        if (!loweredMlir) logs.push('# lowered MLIR output was not produced');
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

      const simArgs = [...this.config.simArgs];
      for (const topName of topModules) {
        simArgs.push('--top', topName);
      }
      // Always request a VCD. UI decides whether to expose Waves based on
      // whether a valid VCD with signal definitions was actually produced.
      simArgs.push('--vcd', wavePath);
      // Trace all signals (default is ports only; @tb has no ports).
      simArgs.push('--trace-all');
      simArgs.push(mlirPath);

      logs.push(formatCommand('circt-sim', simArgs));

      if (typeof onStatus === 'function') onStatus('running');
      const sim = await this._invokeTool('sim', {
        args: simArgs,
        files: {
          [mlirPath]: loweredMlir
        },
        readFiles: [wavePath],
        createDirs: ['/workspace/out']
      });

      if (sim.stdout) logs.push(`[stdout] ${sim.stdout}`);
      if (sim.stderr) logs.push(`[stderr] ${sim.stderr}`);
      appendNonZeroExit(logs, 'circt-sim', sim.exitCode);

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

  async runBmc({ files, top, onStatus = null }) {
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
      logs.push(formatCommand('circt-verilog', compileArgs));

      if (typeof onStatus === 'function') onStatus('compiling');
      let compile;
      try {
        compile = await this._invokeTool('verilog', {
          args: compileArgs,
          files: Object.fromEntries(
            Object.entries(designFiles).map(([path, content]) => [normalizePath(path), content])
          ),
          readFiles: [mlirPath],
          createDirs: ['/workspace/out'],
          uvmManifestUrl
        });
      } catch (error) {
        const text = String(error?.message || error || '');
        if (useFullUvm && text.includes('Aborted(OOM)')) {
          logs.push('# circt-verilog: out of memory compiling UVM — rebuild wasm with larger heap');
          if (typeof onStatus === 'function') onStatus('done');
          return { ok: false, logs };
        }
        throw error;
      }
      if (compile.stdout) logs.push(`[stdout] ${compile.stdout}`);
      if (compile.stderr) logs.push(`[stderr] ${compile.stderr}`);
      appendNonZeroExit(logs, 'circt-verilog', compile.exitCode);

      const mlirText = compile.files?.[mlirPath] || null;
      if (compile.exitCode !== 0 || !mlirText) {
        if (!mlirText) logs.push('# MLIR output was not produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      // Substitute {top} and {input} placeholders in bmc args.
      // DEFAULT_BMC_ARGS writes SMT-LIB to smtPath; read it back after the run.
      const bmcArgs = this.config.bmcArgs.map((arg) =>
        arg.replace('{top}', topModule).replace('{input}', mlirPath)
      );

      logs.push(formatCommand('circt-bmc', bmcArgs));

      if (typeof onStatus === 'function') onStatus('running');
      const bmc = await this._invokeTool('bmc', {
        args: bmcArgs,
        files: { [mlirPath]: mlirText },
        readFiles: [smtPath],
        createDirs: ['/workspace/out']
      });

      if (bmc.stdout) logs.push(`[stdout] ${bmc.stdout}`);
      // Filter the "z3 not found" line — we handle z3 ourselves below.
      const bmcStderr = (bmc.stderr || '')
        .split('\n')
        .filter((l) => !l.includes('z3 not found') && !l.includes('cannot run SMT-LIB'))
        .join('\n')
        .trim();
      if (bmcStderr) logs.push(`[stderr] ${bmcStderr}`);
      appendNonZeroExit(logs, 'circt-bmc', bmc.exitCode);

      const smtlibText = bmc.files?.[smtPath] || null;
      if (!smtlibText) {
        logs.push('# no SMT-LIB output produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      // ── z3 phase ──────────────────────────────────────────────────────────
      const z3out = await evalSmtlib(smtlibText);

      const z3lines = (z3out || '').trim().split('\n').filter(Boolean);
      for (const line of z3lines) logs.push(`[z3] ${line}`);

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

  async runCocotb({ files, top, onStatus = null }) {
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
      logs.push(formatCommand('circt-verilog', compileArgs));

      if (typeof onStatus === 'function') onStatus('compiling');
      const compile = await this._invokeTool('verilog', {
        args: compileArgs,
        files: Object.fromEntries(
          Object.entries(designFiles).map(([path, content]) => [normalizePath(path), content])
        ),
        readFiles: [mlirPath],
        createDirs: ['/workspace/out']
      });
      if (compile.stdout) logs.push(`[stdout] ${compile.stdout}`);
      if (compile.stderr) logs.push(`[stderr] ${compile.stderr}`);
      appendNonZeroExit(logs, 'circt-verilog', compile.exitCode);

      const mlirText = compile.files?.[mlirPath] || null;
      if (compile.exitCode !== 0 || !mlirText) {
        if (!mlirText) logs.push('# MLIR output was not produced');
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
        logs.push('# VPI-capable circt-sim not configured');
        logs.push('# set VITE_CIRCT_SIM_VPI_JS_URL and VITE_CIRCT_SIM_VPI_WASM_URL in .env');
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
        maxTimeNs:  1_000_000
      });

      logs.push(...result.logs);

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

  async runLec({ files, module1, module2, onStatus = null }) {
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
      logs.push(formatCommand('circt-verilog', compileArgs));

      if (typeof onStatus === 'function') onStatus('compiling');
      const compile = await this._invokeTool('verilog', {
        args: compileArgs,
        files: Object.fromEntries(
          Object.entries(designFiles).map(([path, content]) => [normalizePath(path), content])
        ),
        readFiles: [mlirPath],
        createDirs: ['/workspace/out']
      });
      if (compile.stdout) logs.push(`[stdout] ${compile.stdout}`);
      if (compile.stderr) logs.push(`[stderr] ${compile.stderr}`);
      appendNonZeroExit(logs, 'circt-verilog', compile.exitCode);

      const mlirText = compile.files?.[mlirPath] || null;
      if (compile.exitCode !== 0 || !mlirText) {
        if (!mlirText) logs.push('# MLIR output was not produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      const lecArgs = this.config.lecArgs.map((arg) =>
        arg.replace('{module1}', module1)
           .replace('{module2}', module2)
           .replace('{input}', mlirPath)
      );

      logs.push(formatCommand('circt-lec', lecArgs));

      if (typeof onStatus === 'function') onStatus('running');
      const lec = await this._invokeTool('lec', {
        args: lecArgs,
        files: { [mlirPath]: mlirText },
        readFiles: [smtPath],
        createDirs: ['/workspace/out']
      });

      if (lec.stdout) logs.push(`[stdout] ${lec.stdout}`);
      const lecStderr = (lec.stderr || '')
        .split('\n')
        .filter((l) => !l.includes('z3 not found') && !l.includes('cannot run SMT-LIB'))
        .join('\n')
        .trim();
      if (lecStderr) logs.push(`[stderr] ${lecStderr}`);
      appendNonZeroExit(logs, 'circt-lec', lec.exitCode);

      const smtlibText = lec.files?.[smtPath] || null;
      if (!smtlibText) {
        logs.push('# no SMT-LIB output produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      const z3out = await evalSmtlib(smtlibText);

      const z3lines = (z3out || '').trim().split('\n').filter(Boolean);
      for (const line of z3lines) logs.push(`[z3] ${line}`);

      // unsat → no input makes the circuits differ → equivalent.
      // sat   → a distinguishing input exists → not equivalent.
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
