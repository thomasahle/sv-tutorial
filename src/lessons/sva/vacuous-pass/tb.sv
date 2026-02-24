// Testbench that never drives req high — the antecedent never fires.
// The assert reports no failures, but nothing was checked.
module tb;
  logic clk = 0, rst_n = 0;
  logic req = 0, gnt = 0;

  always #5 clk = ~clk;

  vacuous_demo dut(.clk, .rst_n, .req, .gnt);

  initial begin
    @(posedge clk); rst_n = 1;
    // Step 2: uncomment these lines to pulse req and drive gnt within 2 cycles.
    // Watch the cover fire — confirming the property was actually exercised.
    // repeat(3) @(posedge clk);
    // req = 1; @(posedge clk); req = 0;
    // @(posedge clk); gnt = 1; @(posedge clk); gnt = 0;
    repeat (10) @(posedge clk);
    $display("done: did rg_cover fire?");
    $finish;
  end
endmodule
