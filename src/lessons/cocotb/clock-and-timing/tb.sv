// SystemVerilog equivalent of the cocotb test above.
module tb;
  logic       clk = 0, rst = 1;
  logic [3:0] count;
  counter dut(.clk, .rst, .count);

  always #5 clk = ~clk;   // 10 ns period — mirrors: Timer(5, units="ns") in clock_cycle()

  initial begin
    // Reset — mirrors: dut.rst.value = 1; await clock_cycle(dut)
    @(posedge clk); #1;
    rst = 0;

    // Count 5 cycles — mirrors: for _ in range(5): await clock_cycle(dut)
    repeat(5) @(posedge clk);
    #1;

    if (count === 5)
      $display("PASS  count = %0d", count);
    else
      $display("FAIL  count = %0d (expected 5)", count);

    // Reset mid-run — mirrors: dut.rst.value = 1; await clock_cycle(dut)
    rst = 1; @(posedge clk); #1;
    if (count === 0)
      $display("PASS  reset cleared count to 0");
    else
      $display("FAIL  count = %0d after reset (expected 0)", count);

    $finish;
  end
endmodule
