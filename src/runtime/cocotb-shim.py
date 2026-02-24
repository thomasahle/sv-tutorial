"""
Minimal cocotb-compatible API for in-browser simulation via Pyodide + CIRCT WASM VPI.

User-facing API (matches real cocotb):
    import cocotb
    from cocotb.triggers import Timer, RisingEdge, FallingEdge, ClockCycles
    from cocotb.clock import Clock

    @cocotb.test()
    async def my_test(dut):
        dut.A.value = 5
        await Timer(2, units="ns")
        assert dut.X.value == 5

JS calls into Python:
    _vpi_event(trigger_id)        # fires the trigger with that ID
    _start_tests_sync()           # kicks off the test coroutines

Python calls into JS (via 'js' module, set up by cocotb-adapter.js):
    js._cocotb_register_trigger(json)  # register a VPI trigger, returns ID
    js._cocotb_get_signal(name)        # read signal value
    js._cocotb_set_signal(name, val)   # write signal value
    js._cocotb_log(msg)                # emit a log line
    js._cocotb_tests_done()            # signal all tests finished
"""

import asyncio
import json
import sys

# ── Global state ─────────────────────────────────────────────────────────────

_tests = []           # functions registered via @cocotb.test()
_pending = {}         # trigger_id -> asyncio.Event  (registered, not yet fired)
_next_id = 0          # monotonically increasing trigger ID


# ── Utilities ─────────────────────────────────────────────────────────────────

def _to_femtoseconds(time, units):
    scale = {
        'fs': 1,
        'ps': 1_000,
        'ns': 1_000_000,
        'us': 1_000_000_000,
        'ms': 1_000_000_000_000,
        's':  1_000_000_000_000_000,
    }
    return int(float(time) * scale.get(units, 1_000_000))


def _register(trigger_spec):
    """Register a trigger with JS. Returns (id, asyncio.Event)."""
    global _next_id
    tid = _next_id
    _next_id += 1
    event = asyncio.Event()
    _pending[tid] = event
    import js
    js._cocotb_register_trigger(json.dumps({**trigger_spec, 'id': tid}))
    return tid, event


# ── Triggers ──────────────────────────────────────────────────────────────────

class Timer:
    """await Timer(2, units="ns")  — wait for a time delay."""
    def __init__(self, time, units='ns'):
        self._fs = _to_femtoseconds(time, units)

    def __await__(self):
        return self._wait().__await__()

    async def _wait(self):
        _id, event = _register({'type': 'timer', 'fs': self._fs})
        await event.wait()


class RisingEdge:
    """await RisingEdge(dut.clk)  — wait for a rising edge."""
    def __init__(self, signal):
        self._signal = signal

    def __await__(self):
        return self._wait().__await__()

    async def _wait(self):
        _id, event = _register({'type': 'rising_edge', 'signal': self._signal._name})
        await event.wait()


class FallingEdge:
    """await FallingEdge(dut.clk)  — wait for a falling edge."""
    def __init__(self, signal):
        self._signal = signal

    def __await__(self):
        return self._wait().__await__()

    async def _wait(self):
        _id, event = _register({'type': 'falling_edge', 'signal': self._signal._name})
        await event.wait()


class ClockCycles:
    """await ClockCycles(dut.clk, n)  — wait for n rising edges."""
    def __init__(self, signal, num_cycles, rising=True):
        self._signal = signal
        self._n = num_cycles
        self._rising = rising

    def __await__(self):
        return self._wait().__await__()

    async def _wait(self):
        cls = RisingEdge if self._rising else FallingEdge
        for _ in range(self._n):
            await cls(self._signal)


# ── Clock generator ───────────────────────────────────────────────────────────

class Clock:
    """Continuous clock driver. Use with cocotb.start_soon(clock.start())."""
    def __init__(self, signal, period, units='ns'):
        self._signal = signal
        self._half_fs = _to_femtoseconds(period, units) // 2

    async def start(self, start_high=True):
        val = 1 if start_high else 0
        while True:
            self._signal.value = val
            await Timer(self._half_fs, units='fs')
            val = 1 - val


# ── DUT proxy ─────────────────────────────────────────────────────────────────

class _SignalHandle:
    def __init__(self, name):
        self._name = name

    @property
    def value(self):
        import js
        return int(js._cocotb_get_signal(self._name))

    @value.setter
    def value(self, v):
        import js
        js._cocotb_set_signal(self._name, int(v))

    def __repr__(self):
        return f'<Signal {self._name}={self.value}>'


class _DUT:
    def __getattr__(self, name):
        return _SignalHandle(name)


# ── Logger ────────────────────────────────────────────────────────────────────

class _Logger:
    def _emit(self, level, msg):
        import js
        js._cocotb_log(f'[cocotb] {level:5s} {msg}')

    def info(self, msg):    self._emit('INFO',    str(msg))
    def warning(self, msg): self._emit('WARNING', str(msg))
    def error(self, msg):   self._emit('ERROR',   str(msg))
    def debug(self, msg):   self._emit('DEBUG',   str(msg))

log = _Logger()


# ── cocotb module-level API ───────────────────────────────────────────────────

def test():
    """@cocotb.test() decorator — registers a test function."""
    def decorator(fn):
        _tests.append(fn)
        return fn
    return decorator


def start_soon(coro):
    """Launch a coroutine as a background asyncio task."""
    return asyncio.ensure_future(coro)


# ── JS → Python callbacks ─────────────────────────────────────────────────────

def _vpi_event(trigger_id):
    """Called by JS when a VPI callback fires for trigger_id."""
    trigger_id = int(trigger_id)
    event = _pending.pop(trigger_id, None)
    if event is not None:
        event.set()


def _start_tests_sync():
    """Called by JS at cbStartOfSimulation to schedule all tests."""
    asyncio.ensure_future(_run_all())


# ── Test runner ───────────────────────────────────────────────────────────────

async def _run_all():
    import js
    dut = _DUT()
    all_passed = True
    for fn in _tests:
        try:
            await fn(dut)
            js._cocotb_log(f'PASS  {fn.__name__}')
        except AssertionError as e:
            all_passed = False
            js._cocotb_log(f'FAIL  {fn.__name__}: {e}')
        except Exception as e:
            all_passed = False
            js._cocotb_log(f'ERROR {fn.__name__}: {e}')
    js._cocotb_tests_done(all_passed)


# ── Sub-module shims (for "from cocotb.triggers import ..." etc.) ─────────────

class _TriggersModule:
    Timer = Timer
    RisingEdge = RisingEdge
    FallingEdge = FallingEdge
    ClockCycles = ClockCycles

class _ClockModule:
    Clock = Clock

# Register as importable sub-modules in sys.modules
import types
_mod = sys.modules[__name__]  # the cocotb module itself

triggers_mod = types.ModuleType('cocotb.triggers')
triggers_mod.Timer = Timer
triggers_mod.RisingEdge = RisingEdge
triggers_mod.FallingEdge = FallingEdge
triggers_mod.ClockCycles = ClockCycles
sys.modules['cocotb.triggers'] = triggers_mod

clock_mod = types.ModuleType('cocotb.clock')
clock_mod.Clock = Clock
sys.modules['cocotb.clock'] = clock_mod
