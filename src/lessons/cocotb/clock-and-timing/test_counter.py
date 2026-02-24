import cocotb
from cocotb.triggers import Timer


async def clock_cycle(dut, period_ns=10):
    """Drive one full clock period: low → high → settled."""
    dut.clk.value = 0
    await Timer(period_ns // 2, units="ns")
    dut.clk.value = 1
    await Timer(period_ns // 2, units="ns")


@cocotb.test()
async def counter_test(dut):
    dut.clk.value = 0
    dut.rst.value = 1

    # Reset — one posedge with rst high clears the counter
    await clock_cycle(dut)
    dut.rst.value = 0

    # Count 5 cycles
    for _ in range(5):
        await clock_cycle(dut)
    assert dut.count.value == 5, f"Expected 5, got {dut.count.value}"

    # Reset mid-run
    dut.rst.value = 1
    await clock_cycle(dut)
    assert dut.count.value == 0, f"Expected 0 after reset, got {dut.count.value}"
