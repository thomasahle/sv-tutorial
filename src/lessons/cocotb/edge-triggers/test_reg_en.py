import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, ReadOnly, RisingEdge


@cocotb.test()
async def reg_en_test(dut):
    cocotb.start_soon(Clock(dut.clk, 10, unit="ns").start(start_high=False))

    dut.rst.value = 1
    dut.en.value = 0
    dut.d.value = 0
    await RisingEdge(dut.clk)
    await ReadOnly()  # wait for non-blocking assignments to commit
    assert dut.q.value == 0, f"Expected q=0 after reset, got {dut.q.value}"

    await FallingEdge(dut.clk)
    dut.rst.value = 0
    dut.en.value = 1
    dut.d.value = 0xA
    await RisingEdge(dut.clk)
    await ReadOnly()
    assert dut.q.value == 0xA, f"Expected q=10, got {dut.q.value}"

    await FallingEdge(dut.clk)
    dut.en.value = 0
    dut.d.value = 0x3
    await RisingEdge(dut.clk)
    await ReadOnly()
    assert dut.q.value == 0xA, f"q should hold when en=0, got {dut.q.value}"

    await FallingEdge(dut.clk)
    dut.en.value = 1
    dut.d.value = 0x4
    await ClockCycles(dut.clk, 2)
    await ReadOnly()
    assert dut.q.value == 0x4, f"Expected q=4 after load, got {dut.q.value}"
