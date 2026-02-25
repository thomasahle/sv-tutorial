import { CIRCT_FORK_REPO, getCirctRuntimeConfig, getRuntimeBasePath, Z3_SCRIPT_URL } from './circt-config.js';
import COCOTB_SHIM from './cocotb-shim.py?raw';
import { COCOTB_WORKER_SOURCE } from './cocotb-worker-source.js';
import { WORKER_RUNTIME_HELPERS_SOURCE } from './worker-runtime-helpers-source.js';

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

function bundleCompileRoots(files, compileRoots, { enabled = false, force = false } = {}) {
  if (!enabled || !Array.isArray(compileRoots) || compileRoots.length === 0) {
    return { files, roots: compileRoots, bundled: false, rootCount: compileRoots?.length || 0 };
  }
  if (!force && compileRoots.length <= 1) {
    return { files, roots: compileRoots, bundled: false, rootCount: compileRoots?.length || 0 };
  }

  const bundlePath = '/__svt_uvm_bundle.sv';
  const includeLines = compileRoots.map((path) => {
    const normalized = normalizePath(path);
    const relative = normalized.startsWith('/workspace/')
      ? normalized.slice('/workspace/'.length)
      : normalized.replace(/^\/+/, '');
    return `\`include "${relative}"`;
  });

  return {
    files: { ...files, [bundlePath]: `${includeLines.join('\n')}\n` },
    roots: [bundlePath],
    bundled: true,
    rootCount: compileRoots.length,
    bundlePath: normalizePath(bundlePath)
  };
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

function cocotbWorkerLogToStreamEntry(entry) {
  const text = String(entry ?? '');
  if (text.startsWith('[stdout] ') || text.startsWith('[stderr] ')) return text;
  const t = text.trim();
  const isError = /^FAIL\b/.test(t) ||
    /^ERROR\b/.test(t) ||
    /^Traceback\b/.test(t) ||
    /^\w*Error\b/.test(t);
  return `[${isError ? 'stderr' : 'stdout'}] ${text}`;
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

function isWasmOomText(text) {
  return /Aborted\(OOM\)|out of memory|Cannot enlarge memory|cannot grow memory/i.test(
    String(text || '')
  );
}

function isRetryableSimAbortText(text) {
  const value = String(text || '');
  return /Aborted\(/.test(value) || isWasmOomText(value);
}

function isRetryableVerilogCrashText(text) {
  const value = String(text || '');
  return /memory access out of bounds|Malformed attribute storage object|Aborted\(/i.test(value);
}

const UVM_FS_ROOT = '/circt/uvm-core';
const UVM_INCLUDE_ROOT = `${UVM_FS_ROOT}/src`;
const UVM_SIM_MAX_TIME_FS = '1000000';

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

${WORKER_RUNTIME_HELPERS_SOURCE}

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

function getModuleValue(module, name) {
  if (!module) return null;
  const descriptor = Object.getOwnPropertyDescriptor(module, name);
  if (!descriptor || !Object.prototype.hasOwnProperty.call(descriptor, 'value')) return null;
  return descriptor.value;
}

function resolveMain(module) {
  const moduleMain = getModuleValue(module, '_main');
  if (typeof moduleMain === 'function') return moduleMain;
  if (typeof self._main === 'function') return self._main;
  if (typeof globalThis._main === 'function') return globalThis._main;
  return null;
}

function resolveFS(module) {
  const moduleFS = getModuleValue(module, 'FS');
  if (moduleFS && typeof moduleFS.writeFile === 'function' && typeof moduleFS.readFile === 'function') {
    return moduleFS;
  }
  if (self.FS && typeof self.FS.writeFile === 'function' && typeof self.FS.readFile === 'function') {
    return self.FS;
  }
  if (globalThis.FS && typeof globalThis.FS.writeFile === 'function' && typeof globalThis.FS.readFile === 'function') {
    return globalThis.FS;
  }
  return null;
}

function resolveCallMain(module) {
  const moduleCallMain = getModuleValue(module, 'callMain');
  if (typeof moduleCallMain === 'function') return moduleCallMain;
  if (typeof self.__svt_callMain === 'function') return self.__svt_callMain;
  if (typeof globalThis.__svt_callMain === 'function') return globalThis.__svt_callMain;
  if (typeof self.callMain === 'function') return self.callMain;
  if (typeof globalThis.callMain === 'function') return globalThis.callMain;
  return null;
}

function waitForRuntime(timeoutMs = 45000) {
  const start = Date.now();
  return new Promise((resolve, reject) => {
    const tick = () => {
      try {
        const module = self.Module;
        const callMain = resolveCallMain(module);
        const main = resolveMain(module);
        const fsApi = resolveFS(module);

        if (
          circtWorkerRuntimeReady &&
          module &&
          !!callMain &&
          !!main &&
          !!fsApi
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

    let inMemFS = null;
    await loadEmscriptenTool({
      jsUrl: req.jsUrl,
      pathShim: WORKER_PATH_SHIM,
      makeFs: function() {
        // NODERAWFS builds call require('path') / require('fs') at module scope.
        // Provide a Node-like fs backed by memory so tool I/O stays in-worker.
        console.log('[circt-worker] NODERAWFS detected, setting up Node.js emulation');
        inMemFS = makeInMemFS(
          (text) => appendStreamText('stdout', text),
          (text) => appendStreamText('stderr', text)
        );
        return inMemFS;
      },
      onStdout: function(s) { appendStreamText('stdout', s); },
      onStderr: function(s) { appendStreamText('stderr', s); },
      beforeEval: function() { console.log('[circt-worker] starting eval of tool script'); },
      afterEval: function() { console.log('[circt-worker] eval complete'); }
    });

    console.log('[circt-worker] waiting for runtime...');
    const module = await waitForRuntime();
    const fsApi = resolveFS(module);
    if (!fsApi) {
      throw new Error('Emscripten FS runtime did not become ready');
    }
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
        if (typeof fsApi.createLazyFile === 'function') {
          const idx = fsPath.lastIndexOf('/');
          const parent = idx <= 0 ? '/' : fsPath.slice(0, idx);
          const base = idx === -1 ? fsPath : fsPath.slice(idx + 1);
          ensureDir(fsApi, parent);
          try {
            fsApi.createLazyFile(parent, base, sourceUrl, true, false);
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
      writeWorkspaceFiles(fsApi, req.files || {});
      for (const dir of req.createDirs || []) {
        ensureDir(fsApi, dir);
      }
    }

    console.log('[circt-worker] calling callMain with args:', req.args);
    let exitCode = 0;
    try {
      const callMain = resolveCallMain(module);
      if (!callMain) {
        throw new Error('CIRCT runtime is missing callMain entrypoint');
      }
      const ret = callMain(Array.isArray(req.args) ? req.args : []);
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
      : readWorkspaceFiles(fsApi, req.readFiles || []);
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
  onOutput = null,
  signal = null
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

    if (signal) {
      if (signal.aborted) {
        clearTimeout(timeout);
        worker.terminate();
        reject(new DOMException('Run cancelled', 'AbortError'));
        return;
      }
      signal.addEventListener('abort', () => {
        clearTimeout(timeout);
        worker.terminate();
        reject(new DOMException('Run cancelled', 'AbortError'));
      }, { once: true });
    }

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
        await loadScriptOnce(Z3_SCRIPT_URL);
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
    await loadScriptOnce(Z3_SCRIPT_URL);
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
  const ctx = em.ccall('Z3_mk_context', 'number', ['number'], [cfg]);
  em.ccall('Z3_del_config', null, ['number'], [cfg]);
  // Z3_eval_smtlib2_string creates its own internal solver and ignores C-API
  // config params.  The only reliable way to enable model production is to
  // inject the SMT-LIB option into the text itself.
  const text = produceModels
    ? `(set-option :produce-models true)\n${smtlibText}`
    : smtlibText;
  try {
    return em.ccall('Z3_eval_smtlib2_string', 'string', ['number', 'string'], [ctx, text]);
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
  return toAbsoluteUrl(`${getRuntimeBasePath()}circt/uvm-core/uvm-manifest.json`);
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
  pyPath,
  pyCode,
  shimCode,
  maxTimeNs,
  onLogLine = null,
  signal = null
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

    if (signal) {
      if (signal.aborted) {
        clearTimeout(timeout);
        worker.terminate();
        reject(new DOMException('Run cancelled', 'AbortError'));
        return;
      }
      signal.addEventListener('abort', () => {
        clearTimeout(timeout);
        worker.terminate();
        reject(new DOMException('Run cancelled', 'AbortError'));
      }, { once: true });
    }

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

    worker.postMessage({
      simJsUrl,
      simWasmUrl,
      pyodideUrl,
      pageUrl: window.location.href,
      mlir,
      topModule,
      pyPath,
      pyCode,
      shimCode,
      maxTimeNs
    });
  });
}

export class CirctWasmAdapter {
  constructor() {
    this.repo = CIRCT_FORK_REPO;
    this.config = getCirctRuntimeConfig();
    this.ready = false;
    this._runController = null;
  }

  cancel() {
    this._runController?.abort();
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
      onOutput,
      signal: this._runController?.signal ?? null
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
    this._runController = new AbortController();
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

      const topModules = pickTopModules(files, top);
      const mlirPath = '/workspace/out/design.llhd.mlir';
      const wavePath = '/workspace/out/waves.vcd';
      const useFullUvm = needsUvmLibrary(files);
      const uvmManifestUrl = useFullUvm ? getUvmManifestUrl() : null;

      const compileRootPaths = compileRootSourcePaths(files);
      const buildCompilePlan = ({ forceBundle, singleUnit, label }) => {
        const bundledCompile = bundleCompileRoots(files, compileRootPaths, {
          enabled: useFullUvm,
          force: useFullUvm ? forceBundle : false
        });
        const compileRoots = (bundledCompile.roots || []).map((path) => normalizePath(path));
        let compileArgs = [...this.config.verilogArgs];
        compileArgs = singleUnit
          ? (compileArgs.includes('--single-unit') ? compileArgs : [...compileArgs, '--single-unit'])
          : removeFlag(compileArgs, '--single-unit');
        if (useFullUvm) {
          compileArgs.push('--uvm-path', UVM_FS_ROOT, '-I', UVM_INCLUDE_ROOT);
        }
        for (const topName of topModules) {
          compileArgs.push('--top', topName);
        }
        compileArgs.push('-o', mlirPath, ...compileRoots);
        return {
          label,
          bundledCompile,
          compileArgs,
          workspaceFiles: Object.fromEntries(
            Object.entries(bundledCompile.files).map(([path, content]) => [normalizePath(path), content])
          )
        };
      };

      const compilePlans = useFullUvm
        ? [
            buildCompilePlan({ forceBundle: true, singleUnit: true, label: 'bundled single-unit mode' }),
            buildCompilePlan({ forceBundle: false, singleUnit: false, label: 'native root mode' }),
            buildCompilePlan({ forceBundle: true, singleUnit: false, label: 'bundled non-single-unit mode' }),
            buildCompilePlan({ forceBundle: false, singleUnit: true, label: 'single-unit mode' }),
          ]
        : [
            buildCompilePlan({
              forceBundle: false,
              singleUnit: this.config.verilogArgs.includes('--single-unit'),
              label: 'default mode'
            })
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

      if (typeof onStatus === 'function') onStatus('compiling');
      let compile = null;
      let loweredMlir = null;
      for (let attempt = 0; attempt < compilePlans.length; attempt += 1) {
        const plan = compilePlans[attempt];
        if (attempt > 0) {
          emitLog(`# circt-verilog: retrying in ${plan.label}`);
        }
        if (plan.bundledCompile.bundled) {
          emitLog(
            `# bundled ${plan.bundledCompile.rootCount} roots into ${plan.bundledCompile.bundlePath} ` +
            'for stable UVM compilation'
          );
        }
        emitLog(formatCommand('circt-verilog', plan.compileArgs));

        const compileStream = makeToolOutputHandler();
        let attemptCompile;
        try {
          attemptCompile = await this._invokeTool('verilog', {
            args: plan.compileArgs,
            files: plan.workspaceFiles,
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
          const canRetry = useFullUvm && attempt + 1 < compilePlans.length && isRetryableVerilogCrashText(text);
          if (canRetry) continue;
          throw error;
        }
        if (!compileStream.sawStream()) {
          if (attemptCompile.stdout) emitLog(`[stdout] ${attemptCompile.stdout}`);
          if (attemptCompile.stderr) emitLog(`[stderr] ${attemptCompile.stderr}`);
        }
        appendNonZeroExit(logs, 'circt-verilog', attemptCompile.exitCode, emitLog);

        const rawMlir = attemptCompile.files?.[mlirPath] || null;
        // Add name attributes to llhd.sig ops that lack them so circt-sim's VCD
        // writer can emit $var entries. circt-verilog only sets name on module
        // port connections; testbench-level logic signals get no name attribute.
        // We use the SSA result identifier (%clk → name "clk") as the signal name.
        const attemptLoweredMlir = rawMlir
          ? rawMlir.replace(
              /(%([a-zA-Z_]\w*)\s*=\s*llhd\.sig\s+)(?!name\s+")/g,
              (_m, prefix, sigName) => `${prefix}name "${sigName}" `
            )
          : null;
        if (attemptCompile.exitCode === 0 && attemptLoweredMlir) {
          compile = attemptCompile;
          loweredMlir = attemptLoweredMlir;
          break;
        }

        const canRetry = useFullUvm && attempt + 1 < compilePlans.length &&
          isRetryableVerilogCrashText(attemptCompile.stderr || '');
        if (canRetry) continue;
        if (!attemptLoweredMlir) emitLog('# lowered MLIR output was not produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs, waveform: null };
      }
      if (!compile || !loweredMlir) {
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

      if (typeof onStatus === 'function') onStatus('running');
      const simStream = makeToolOutputHandler();
      const runSimAttempt = async ({ withTraceAll, withVcd }) => {
        const simArgs = forceInterpretSimMode([...this.config.simArgs]);
        for (const topName of topModules) {
          simArgs.push('--top', topName);
        }
        if (useFullUvm) {
          simArgs.push('--max-time', UVM_SIM_MAX_TIME_FS);
        }
        if (withVcd) simArgs.push('--vcd', wavePath);
        if (withTraceAll) simArgs.push('--trace-all');
        simArgs.push(mlirPath);

        emitLog(formatCommand('circt-sim', simArgs));
        const sim = await this._invokeTool('sim', {
          args: simArgs,
          files: {
            [mlirPath]: loweredMlir
          },
          readFiles: withVcd ? [wavePath] : [],
          createDirs: ['/workspace/out'],
          onOutput: simStream.onOutput
        });
        if (sim.exitCode !== 0 && isRetryableSimAbortText(sim.stderr)) {
          throw new Error(String(sim.stderr || `circt-sim exited ${sim.exitCode}`));
        }
        return { sim, withVcd };
      };

      let simResult;
      try {
        simResult = await runSimAttempt({ withTraceAll: true, withVcd: true });
      } catch (error) {
        const retryable = isRetryableSimAbortText(error?.message || error);
        if (!retryable) throw error;
        emitLog('# circt-sim: runtime abort with --trace-all; retrying without --trace-all');
        try {
          simResult = await runSimAttempt({ withTraceAll: false, withVcd: true });
        } catch (retryError) {
          const retryableNoTrace = isRetryableSimAbortText(retryError?.message || retryError);
          if (!retryableNoTrace) throw retryError;
          emitLog('# circt-sim: runtime abort while writing VCD; retrying without waveform capture');
          simResult = await runSimAttempt({ withTraceAll: false, withVcd: false });
        }
      }

      const sim = simResult.sim;

      if (!simStream.sawStream()) {
        if (sim.stdout) emitLog(`[stdout] ${sim.stdout}`);
        if (sim.stderr) emitLog(`[stderr] ${sim.stderr}`);
      }
      appendNonZeroExit(logs, 'circt-sim', sim.exitCode, emitLog);

      const rawVcdText = simResult.withVcd ? sim.files?.[wavePath] || null : null;
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
      if (error.name === 'AbortError') return { ok: false, logs: [], waveform: null };
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
    this._runController = new AbortController();
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
      const uvmManifestUrl = useFullUvm ? getUvmManifestUrl() : null;
      const bundledCompile = bundleCompileRoots(designFiles, compileRootSourcePaths(designFiles), {
        enabled: useFullUvm,
        force: useFullUvm
      });
      const compileRoots = bundledCompile.roots;

      // Use the provided top name directly — don't let pickTopModules pick 'tb'.
      const topModule = top || filename(userSvPaths[0]).replace(/\.[^.]+$/, '');
      const mlirPath = '/workspace/out/design.mlir';
      const smtPath = '/workspace/out/check.smt2';

      const compileArgs = [
        ...this.config.verilogArgs,
        ...(useFullUvm && !this.config.verilogArgs.includes('--single-unit')
          ? ['--single-unit']
          : []),
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
      if (bundledCompile.bundled) {
        emitLog(
          `# bundled ${bundledCompile.rootCount} roots into ${bundledCompile.bundlePath} ` +
          'for stable UVM compilation'
        );
      }
      emitLog(formatCommand('circt-verilog', compileArgs));

      if (typeof onStatus === 'function') onStatus('compiling');
      let compile;
      const compileStream = makeToolOutputHandler();
      try {
        compile = await this._invokeTool('verilog', {
          args: compileArgs,
          files: Object.fromEntries(
            Object.entries(bundledCompile.files).map(([path, content]) => [normalizePath(path), content])
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
      if (error.name === 'AbortError') return { ok: false, logs: [] };
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
    this._runController = new AbortController();
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
      const [pyPath, pyCode] = pyEntries[0];

      // Check that the VPI sim is configured.
      const simVpi = this.config.toolchain.simVpi;
      if (!simVpi?.js || !simVpi?.wasm) {
        emitLog('# VPI-capable circt-sim not configured');
        emitLog('# set VITE_CIRCT_SIM_VPI_JS_URL and VITE_CIRCT_SIM_VPI_WASM_URL in .env');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs };
      }

      if (typeof onStatus === 'function') onStatus('running');

      let sawWorkerStream = false;
      const result = await runCocotbInWorker({
        simJsUrl:   toAbsoluteUrl(simVpi.js),
        simWasmUrl: toAbsoluteUrl(simVpi.wasm),
        pyodideUrl: toAbsoluteUrl(this.config.pyodideUrl),
        mlir:       mlirText,
        topModule,
        pyPath:     normalizePath(pyPath),
        pyCode,
        shimCode:   COCOTB_SHIM,
        maxTimeNs:  1_000_000,
        signal:     this._runController?.signal ?? null,
        onLogLine:  (line) => {
          sawWorkerStream = true;
          emitLog(cocotbWorkerLogToStreamEntry(line));
        }
      });

      if (!sawWorkerStream && Array.isArray(result.logs) && result.logs.length) {
        for (const rawLine of result.logs) {
          emitLog(cocotbWorkerLogToStreamEntry(rawLine));
        }
      }

      if (typeof onStatus === 'function') onStatus('done');
      return { ok: result.ok, logs, waveform: null };

    } catch (error) {
      if (typeof onStatus === 'function') onStatus('done');
      if (error.name === 'AbortError') return { ok: false, logs: [] };
      return {
        ok: false,
        logs: [String(error?.message || error)]
      };
    }
  }

  async runLec({ files, module1, module2, onStatus = null, onLog = null }) {
    this._runController = new AbortController();
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

      emitLog(`$ z3 ${smtPath}`);
      const z3out = await evalSmtlib(smtlibText);

      const z3lines = (z3out || '').trim().split('\n').filter(Boolean);
      for (const line of z3lines) emitLog(line);

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
          emitLog(`$ z3 -model ${smtPath} | grep define-fun`);
          const freshEm = await getFreshZ3Module();
          // Insert (get-model) before (reset) — circt-lec SMT-LIB ends with
          // (reset) which clears solver state; appending after it loses the model.
          const resetIdx = smtlibText.lastIndexOf('(reset)');
          const smtWithModel = resetIdx >= 0
            ? smtlibText.slice(0, resetIdx) + '(get-model)\n' + smtlibText.slice(resetIdx)
            : smtlibText + '\n(get-model)\n';
          const modelOut = await evalSmtlib(smtWithModel, { produceModels: true, em: freshEm });
          // Collapse whitespace so multi-line define-fun entries match as one unit.
          const modelFlat = (modelOut || '').replace(/\s+/g, ' ');
          const assignments = [];
          // BitVec: (define-fun |name| () (_ BitVec N) #xVAL)
          const bvRe = /\(define-fun\s+\|?(\S+?)\|?\s+\(\)\s+\(_\s+BitVec\s+(\d+)\)\s+(#x[0-9a-fA-F]+|#b[01]+)\s*\)/g;
          let m;
          while ((m = bvRe.exec(modelFlat)) !== null) {
            const [, name, widthStr, val] = m;
            // Emit the raw define-fun line (what grep would show).
            emitLog(`  (define-fun ${name} () (_ BitVec ${widthStr}) ${val})`);
            // Skip circuit-specific output variables (c1_…, c2_…) — show only inputs.
            if (/^c\d+_/.test(name)) continue;
            const width = parseInt(widthStr, 10);
            const raw = val.startsWith('#x') ? parseInt(val.slice(2), 16) : parseInt(val.slice(2), 2);
            // CIRCT encodes N-bit SV signals as 2N-bit SMT bitvectors: the lower N
            // bits are "unknown" flags and the upper N bits are the logic values.
            // Decode to the plain N-bit value when all unknown bits are zero.
            let displayVal = raw;
            if (width % 2 === 0) {
              const half = width / 2;
              const unknownMask = (1 << half) - 1;
              if ((raw & unknownMask) === 0) displayVal = (raw >> half) & unknownMask;
            }
            assignments.push(`${name}=${displayVal}`);
          }
          // Bool: (define-fun |name| () Bool true/false)
          const boolRe = /\(define-fun\s+\|?(\S+?)\|?\s+\(\)\s+Bool\s+(true|false)\s*\)/g;
          while ((m = boolRe.exec(modelFlat)) !== null) {
            emitLog(`  (define-fun ${m[1]} () Bool ${m[2]})`);
            if (/^c\d+_/.test(m[1])) continue;
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
      if (error.name === 'AbortError') return { ok: false, logs: [] };
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

let _adapter = null;
export function getCirctWasmAdapter() {
  _adapter ??= createCirctWasmAdapter();
  return _adapter;
}
