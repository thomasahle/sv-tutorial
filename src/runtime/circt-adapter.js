import { CIRCT_FORK_REPO, getCirctRuntimeConfig } from './circt-config.js';

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

function sourcePathsFromWorkspace(files) {
  return Object.keys(files)
    .filter((path) => ['.sv', '.svh', '.v'].includes(ext(path)))
    .sort();
}

function containsPath(files, basename) {
  return Object.keys(files).some((path) => filename(path).toLowerCase() === basename.toLowerCase());
}

function hasVcdSignalDefinitions(vcdText) {
  return typeof vcdText === 'string' && /\$var\b/.test(vcdText);
}

function pickTopModules(files, fallbackTop) {
  if (containsPath(files, 'hdl_top.sv') && containsPath(files, 'hvl_top.sv')) {
    return ['hdl_top', 'hvl_top'];
  }
  if (containsPath(files, 'tb.sv')) {
    return ['tb'];
  }
  if (fallbackTop) {
    return [fallbackTop];
  }
  if (containsPath(files, 'top.sv')) {
    return ['top'];
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
  var dirs = new Set(['/', '/dev', '/workspace', '/workspace/src', '/workspace/out']);
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
      if (store[path]) {
        var enc = (typeof opts === 'string') ? opts : (opts && opts.encoding);
        return enc ? new TextDecoder().decode(store[path]) : store[path];
      }
      // Synchronous XHR fallback for URLs not in the store (e.g. the WASM binary).
      try {
        var xhr = new XMLHttpRequest();
        xhr.open('GET', path, false /* synchronous */);
        xhr.responseType = 'arraybuffer';
        xhr.send(null);
        if (xhr.status === 200 || xhr.status === 0) {
          var bytes = new Uint8Array(xhr.response);
          var enc2 = (typeof opts === 'string') ? opts : (opts && opts.encoding);
          return enc2 ? new TextDecoder().decode(bytes) : bytes;
        }
      } catch(fetchErr) {}
      var e = new Error('ENOENT: no such file or directory, open \'' + path + '\'');
      e.code = 'ENOENT'; throw e;
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

function runToolInWorker({ jsUrl, wasmUrl, args, files, readFiles, createDirs = [] }) {
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

    worker.postMessage({ jsUrl, wasmUrl, args, files, readFiles, createDirs });
  });
}

function toAbsoluteUrl(rawUrl) {
  try {
    return new URL(rawUrl, window.location.href).href;
  } catch {
    return rawUrl;
  }
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

  async _invokeTool(toolName, { args, files = {}, readFiles = [], createDirs = [] }) {
    const tool = this.config.toolchain[toolName];
    if (!tool) throw new Error(`Unknown CIRCT tool: ${toolName}`);

    return runToolInWorker({
      jsUrl: toAbsoluteUrl(tool.js),
      wasmUrl: toAbsoluteUrl(tool.wasm),
      args,
      files,
      readFiles,
      createDirs
    });
  }

  async selfCheck({ lesson = null } = {}) {
    const logs = [`[circt] self-check starting`, `[circt] configured fork ${this.repo}`];

    try {
      await this.init();

      const verilogHelp = await this._invokeTool('verilog', {
        args: ['--help']
      });
      logs.push(`[circt] verilog runtime: ${this.config.toolchain.verilog.js}`);
      logs.push(`[circt] verilog --help exit code: ${verilogHelp.exitCode}`);

      const simHelp = await this._invokeTool('sim', {
        args: ['--help']
      });
      logs.push(`[circt] sim runtime: ${this.config.toolchain.sim.js}`);
      logs.push(`[circt] sim --help exit code: ${simHelp.exitCode}`);

      const ok = verilogHelp.exitCode === 0 && simHelp.exitCode === 0;
      if (verilogHelp.stderr) logs.push(`[stderr] ${verilogHelp.stderr}`);
      if (simHelp.stderr) logs.push(`[stderr] ${simHelp.stderr}`);

      return { ok, logs };
    } catch (error) {
      return {
        ok: false,
        logs: [...logs, `[circt] self-check failed: ${error.message}`]
      };
    }
  }

  async run({ files, top, waveform, onStatus = null }) {
    const startLog = `[circt] using fork ${this.repo}`;

    try {
      await this.init();

      const svPaths = sourcePathsFromWorkspace(files);
      if (!svPaths.length) {
        if (typeof onStatus === 'function') onStatus('done');
        return {
          ok: false,
          logs: [startLog, '[circt] no SystemVerilog source files found in workspace'],
          waveform: null
        };
      }

      const topModules = pickTopModules(files, top);
      const normalizedSvPaths = svPaths.map((path) => normalizePath(path));
      const mlirPath = '/workspace/out/design.llhd.mlir';
      const wavePath = '/workspace/out/waves.vcd';

      const compileArgs = [...this.config.verilogArgs];
      for (const topName of topModules) {
        compileArgs.push('--top', topName);
      }
      compileArgs.push('-o', mlirPath, ...normalizedSvPaths);

      if (typeof onStatus === 'function') onStatus('compiling');
      const compile = await this._invokeTool('verilog', {
        args: compileArgs,
        files: Object.fromEntries(Object.entries(files).map(([path, content]) => [normalizePath(path), content])),
        readFiles: [mlirPath],
        createDirs: ['/workspace/out']
      });

      const logs = [
        startLog,
        '[circt] compile finished',
        `[circt] compile args: ${compileArgs.join(' ')}`
      ];
      if (compile.stdout) logs.push(`[stdout] ${compile.stdout}`);
      if (compile.stderr) logs.push(`[stderr] ${compile.stderr}`);
      logs.push(`[circt] compile exit code: ${compile.exitCode}`);

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
        if (!loweredMlir) logs.push('[circt] lowered MLIR output was not produced');
        if (typeof onStatus === 'function') onStatus('done');
        return { ok: false, logs, waveform: null };
      }

      const shouldSimulate = waveform !== 'off' || containsPath(files, 'tb.sv');
      if (!shouldSimulate) {
        logs.push('[circt] no simulation requested for this lesson');
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
      if (waveform !== 'off') {
        simArgs.push('--vcd', wavePath);
        // Trace all signals (default is ports only; @tb has no ports).
        simArgs.push('--trace-all');
      }
      simArgs.push(mlirPath);

      if (typeof onStatus === 'function') onStatus('running');
      const sim = await this._invokeTool('sim', {
        args: simArgs,
        files: {
          [mlirPath]: loweredMlir
        },
        readFiles: waveform !== 'off' ? [wavePath] : [],
        createDirs: ['/workspace/out']
      });

      if (sim.stdout) logs.push(`[stdout] ${sim.stdout}`);
      if (sim.stderr) logs.push(`[stderr] ${sim.stderr}`);
      logs.push(`[circt] sim exit code: ${sim.exitCode}`);

      const rawVcdText = waveform !== 'off' ? sim.files?.[wavePath] || null : null;
      const vcdText = hasVcdSignalDefinitions(rawVcdText) ? rawVcdText : null;
      if (waveform !== 'off') {
        if (vcdText) {
          logs.push('[circt] waveform generated');
        } else {
          logs.push('[circt] no waveform vcd found');
          if (rawVcdText) {
            logs.push('[circt] waveform vcd is missing $var signal definitions');
          }
        }
      }

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
          startLog,
          `[circt] runtime unavailable: ${error.message}`,
          `[circt] verilog js: ${this.config.toolchain.verilog.js}`,
          `[circt] verilog wasm: ${this.config.toolchain.verilog.wasm}`,
          `[circt] sim js: ${this.config.toolchain.sim.js}`,
          `[circt] sim wasm: ${this.config.toolchain.sim.wasm}`,
          '[circt] run scripts/setup-circt.sh and npm run sync:circt to refresh artifacts'
        ],
        waveform: null
      };
    }
  }
}

export function createCirctWasmAdapter() {
  return new CirctWasmAdapter();
}
