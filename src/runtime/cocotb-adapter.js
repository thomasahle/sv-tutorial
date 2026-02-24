/**
 * cocotb-adapter.js — in-browser cocotb execution via Pyodide + CIRCT WASM VPI
 *
 * Architecture:
 *   1. Compile SV → LLHD MLIR  (circt-verilog, existing batch WASM)
 *   2. Load Pyodide, install cocotb shim, run user's .py test file
 *   3. VPI coordination loop:
 *      - circt-sim WASM (VPI build) fires callbacks via circt_vpi_callback_to_js
 *      - JS routes events to Python (via Pyodide), registers next VPI triggers
 *      - Loop until simulation ends
 *
 * The circt-sim VPI WASM exports (via Asyncify + EXPORTED_FUNCTIONS):
 *   Module._vpi_register_cb(cb_data_ptr)
 *   Module._vpi_handle_by_name(name_ptr, scope)
 *   Module._vpi_put_value(handle, value_ptr, time_ptr, flags)
 *   Module._vpi_get_value(handle, value_ptr)
 *   Module._vpi_get_time(handle, time_ptr)
 *   Module._vpi_control(op, ...)
 *   Module.circt_vpi_callback_to_js  ← Asyncify import (set before load)
 *
 * VPI callback reasons (IEEE 1800):
 */
const VPI = {
  cbValueChange:        1,
  cbStmt:               2,
  cbForce:              3,
  cbRelease:            4,
  cbAtStartOfSimTime:   5,
  cbReadWriteSynch:     6,
  cbReadOnlySynch:      7,
  cbNextSimTime:        8,
  cbAfterDelay:         9,
  cbEndOfCompile:       10,
  cbStartOfSimulation:  11,
  cbEndOfSimulation:    12,
  cbError:              13,
  vpiFinish:            66,
  vpiStop:              67,
  // vpi_get value formats
  vpiIntVal:            1,
  // vpi_time types
  vpiSimTime:           1,
  vpiScaledRealTime:    2,
};

// ── WASM memory helpers ──────────────────────────────────────────────────────

function writeString(Module, str) {
  const bytes = new TextEncoder().encode(str + '\0');
  const ptr = Module._malloc(bytes.length);
  Module.HEAPU8.set(bytes, ptr);
  return ptr;
}

function allocStruct(Module, size) {
  return Module._malloc(size);
}

function free(Module, ptr) {
  Module._free(ptr);
}

/** Write a s_cb_data struct and return pointer. Layout (32-bit WASM):
 *  0: reason (i32)
 *  4: cb_rtn (ptr, function pointer)
 *  8: obj (ptr)
 * 12: time (ptr → s_vpi_time)
 * 16: value (ptr)
 * 20: index (i32)
 * 24: user_data (ptr)
 * Total: 28 bytes
 */
function makeCbData(Module, { reason, cbRtn = 0, obj = 0, time = 0, value = 0, userData = 0 }) {
  const ptr = Module._malloc(28);
  Module.setValue(ptr +  0, reason,   'i32');
  Module.setValue(ptr +  4, cbRtn,    'i32');
  Module.setValue(ptr +  8, obj,      'i32');
  Module.setValue(ptr + 12, time,     'i32');
  Module.setValue(ptr + 16, value,    'i32');
  Module.setValue(ptr + 20, 0,        'i32');
  Module.setValue(ptr + 24, userData, 'i32');
  return ptr;
}

/** Write a s_vpi_time struct (vpiSimTime). Layout:
 *  0: type (i32)
 *  4: high (u32)
 *  8: low  (u32)
 * 12: real (double, 8 bytes)
 * Total: 20 bytes
 */
function makeVpiTime(Module, fs) {
  // Convert femtoseconds to ps (circt-sim uses ps internally for vpiSimTime)
  const ps = BigInt(fs) / 1000n;
  const hi = Number(ps >> 32n) >>> 0;
  const lo = Number(ps & 0xFFFFFFFFn) >>> 0;
  const ptr = Module._malloc(20);
  Module.setValue(ptr +  0, VPI.vpiSimTime, 'i32');
  Module.setValue(ptr +  4, hi,             'i32');
  Module.setValue(ptr +  8, lo,             'i32');
  Module.setValue(ptr + 12, 0,              'double');
  return ptr;
}

/** Write a s_vpi_value struct (vpiIntVal). Layout:
 *  0: format (i32)
 *  4: value.integer (i32)  ← union, 8 bytes total
 * Total: 12 bytes
 */
function makeVpiValue(Module, intVal) {
  const ptr = Module._malloc(12);
  Module.setValue(ptr + 0, VPI.vpiIntVal, 'i32');
  Module.setValue(ptr + 4, intVal,        'i32');
  Module.setValue(ptr + 8, 0,             'i32');
  return ptr;
}

function readVpiIntValue(Module, valuePtr) {
  return Module.getValue(valuePtr + 4, 'i32');
}

// ── Trigger registration ─────────────────────────────────────────────────────

/**
 * Register a VPI callback for a trigger spec from Python.
 * Returns the vpiHandle (used to map back when the callback fires).
 *
 * triggerSpec: { type: 'timer'|'rising_edge'|'falling_edge', id, fs?, signal? }
 */
function registerVpiTrigger(Module, triggerSpec, cbFnPtr) {
  const { type, id, fs, signal } = triggerSpec;

  if (type === 'timer') {
    const timePtr = makeVpiTime(Module, BigInt(fs));
    const cbData = makeCbData(Module, {
      reason: VPI.cbAfterDelay,
      cbRtn:  cbFnPtr,
      time:   timePtr,
      userData: id,
    });
    const handle = Module._vpi_register_cb(cbData);
    free(Module, timePtr);
    free(Module, cbData);
    return handle;
  }

  if (type === 'rising_edge' || type === 'falling_edge') {
    const namePtr = writeString(Module, signal);
    const sigHandle = Module._vpi_handle_by_name(namePtr, 0);
    free(Module, namePtr);

    const cbData = makeCbData(Module, {
      reason: VPI.cbValueChange,
      cbRtn:  cbFnPtr,
      obj:    sigHandle,
      userData: id,
    });
    const handle = Module._vpi_register_cb(cbData);
    free(Module, cbData);
    return handle;
  }

  console.warn('[cocotb] Unknown trigger type:', type);
  return 0;
}

/**
 * Read signal value from WASM via VPI.
 */
function vpiGetSignalValue(Module, signalName) {
  const namePtr = writeString(Module, signalName);
  const handle = Module._vpi_handle_by_name(namePtr, 0);
  free(Module, namePtr);
  if (!handle) return 0;

  const valuePtr = makeVpiValue(Module, 0);
  Module._vpi_get_value(handle, valuePtr);
  const result = readVpiIntValue(Module, valuePtr);
  free(Module, valuePtr);
  return result;
}

/**
 * Write signal value to WASM via VPI.
 */
function vpiSetSignalValue(Module, signalName, intVal) {
  const namePtr = writeString(Module, signalName);
  const handle = Module._vpi_handle_by_name(namePtr, 0);
  free(Module, namePtr);
  if (!handle) return;

  const valuePtr = makeVpiValue(Module, intVal);
  Module._vpi_put_value(handle, valuePtr, 0, 0);
  free(Module, valuePtr);
}

// ── Main cocotb runner ───────────────────────────────────────────────────────

/**
 * Run a cocotb Python test against a compiled MLIR design.
 *
 * @param {object} opts
 *   simModule    – initialized circt-sim WASM Module (with VPI + Asyncify)
 *   mlir         – LLHD MLIR text (string)
 *   topModule    – top module name (string)
 *   pyCode       – the user's Python test file (string)
 *   shimCode     – cocotb-shim.py source (string)
 *   pyodideUrl   – URL to pyodide.js (string)
 *   onLog        – (msg: string) => void
 *   maxTimeNs    – simulation time limit in ns (default: 1_000_000)
 */
export async function runCocotbTest({
  simModule,
  mlir,
  topModule,
  pyCode,
  shimCode,
  pyodideUrl,
  onLog,
  maxTimeNs = 1_000_000,
}) {
  // ── 1. Load Pyodide ───────────────────────────────────────────────────────
  onLog('[pyodide] Loading...');
  importScripts(pyodideUrl);
  const pyodide = await loadPyodide({ stdout: onLog, stderr: onLog });
  onLog('[pyodide] Ready');

  // ── 2. Install cocotb shim ────────────────────────────────────────────────
  // Register JS functions Python can call
  globalThis._cocotb_register_trigger = (jsonStr) => {
    const spec = JSON.parse(jsonStr);
    // Will be consumed by the VPI coordination loop
    _pendingRegistrations.push(spec);
  };
  globalThis._cocotb_get_signal = (name) => vpiGetSignalValue(simModule, name);
  globalThis._cocotb_set_signal = (name, val) => vpiSetSignalValue(simModule, name, val);
  globalThis._cocotb_log = (msg) => onLog(msg);
  globalThis._cocotb_tests_done = () => { _testsDone = true; };

  // Install shim as 'cocotb' module in Pyodide
  pyodide.runPython(shimCode);
  // The shim registers itself into sys.modules['cocotb'] etc. via the last block.
  // We also need to make the shim's namespace available as 'cocotb':
  pyodide.runPython(`import sys; sys.modules['cocotb'] = sys.modules[__name__]`);

  // Execute user's Python test file (registers @cocotb.test() functions)
  try {
    pyodide.runPython(pyCode);
  } catch (e) {
    onLog(`[cocotb] Python error: ${e}`);
    return { ok: false };
  }

  // ── 3. Write MLIR to WASM FS and init simulation ──────────────────────────
  const mlirPtr = writeString(simModule, mlir);
  // (In practice, write to WASM virtual FS and invoke main() with the path)
  // For now the caller pre-initializes the WASM module; we just drive callbacks.
  free(simModule, mlirPtr);

  // ── 4. Add a dummy function pointer for VPI callbacks ────────────────────
  // When VPI fires a callback, circt_vpi_callback_to_js is called (Asyncify).
  // We intercept it here. The cbRtn field in cb_data is unused in our bridge
  // (JS handles everything), so we register a no-op function pointer.
  const noopFnPtr = simModule.addFunction(() => 0, 'ii');

  // ── 5. VPI coordination state ─────────────────────────────────────────────
  let _pendingRegistrations = [];  // trigger specs from Python, not yet registered
  let _testsDone = false;
  let _valueChangeEdges = new Map(); // signal → last value (for edge detection)

  // Rebuild reference (closures capture the outer let; reassign after reset)
  globalThis._cocotb_register_trigger = (jsonStr) => {
    _pendingRegistrations.push(JSON.parse(jsonStr));
  };
  globalThis._cocotb_tests_done = () => { _testsDone = true; };

  /**
   * Register all pending VPI triggers from Python.
   */
  function flushRegistrations() {
    for (const spec of _pendingRegistrations) {
      registerVpiTrigger(simModule, spec, noopFnPtr);
    }
    _pendingRegistrations = [];
  }

  /**
   * Called by Emscripten when circt-sim's VPI runtime fires a callback.
   * reason    – VPI callback reason (e.g. VPI.cbStartOfSimulation)
   * cbDataPtr – pointer to s_cb_data in WASM heap
   *
   * This is the Asyncify import: returning resolves the suspension and
   * resumes the simulation.
   */
  simModule['circt_vpi_callback_to_js'] = async function(reason, cbDataPtr) {
    if (reason === VPI.cbStartOfSimulation) {
      // Start Python tests as asyncio background tasks
      pyodide.runPython('_start_tests_sync()');

      // Give asyncio one tick so tests start running and register first triggers
      await pyodide.runPythonAsync('await __import__("asyncio").sleep(0)');

    } else if (reason === VPI.cbEndOfSimulation) {
      return; // nothing to do

    } else {
      // A trigger fired. Read which trigger_id fired from cb_data.user_data.
      const triggerId = simModule.getValue(cbDataPtr + 24, 'i32');

      // For value-change callbacks, check edge direction before notifying Python
      if (reason === VPI.cbValueChange && cbDataPtr) {
        const sigHandle = simModule.getValue(cbDataPtr + 8, 'i32');
        if (sigHandle) {
          const valPtr = makeVpiValue(simModule, 0);
          simModule._vpi_get_value(sigHandle, valPtr);
          const newVal = readVpiIntValue(simModule, valPtr);
          free(simModule, valPtr);
          const lastVal = _valueChangeEdges.get(triggerId) ?? -1;
          _valueChangeEdges.set(triggerId, newVal);

          // Only fire rising/falling edges when direction matches
          // (The trigger spec tells us which direction we want)
          // For now fire unconditionally — the shim handles direction filtering
        }
      }

      // Notify Python that this trigger fired
      pyodide.runPython(`_vpi_event(${triggerId})`);

      // Give asyncio iterations to process the event and register the next trigger
      // Multiple iterations handle concurrent tasks (e.g. Clock + test)
      for (let i = 0; i < 20; i++) {
        await pyodide.runPythonAsync('await __import__("asyncio").sleep(0)');
        if (_pendingRegistrations.length > 0 || _testsDone) break;
      }
    }

    if (_testsDone) {
      // Tell simulator to stop
      simModule._vpi_control(VPI.vpiFinish, 0);
      return;
    }

    // Register whatever triggers Python queued up
    flushRegistrations();
  };

  // ── 6. Register cbStartOfSimulation and start simulation ─────────────────
  const startCbData = makeCbData(simModule, {
    reason: VPI.cbStartOfSimulation,
    cbRtn: noopFnPtr,
  });
  simModule._vpi_register_cb(startCbData);
  free(simModule, startCbData);

  const maxTimePs = maxTimeNs * 1_000;  // ns → ps
  const args = [
    'circt-sim',
    '--resource-guard=false',
    '--mode', 'interpret',
    `--max-time=${maxTimePs}`,
    '--top', topModule,
    '/workspace/out/design.llhd.mlir',
  ];

  // callMain returns a Promise (Asyncify); it suspends whenever
  // circt_vpi_callback_to_js is called and resumes when it resolves.
  await simModule.callMain(args);

  return { ok: !_testsDone ? false : true };
}
