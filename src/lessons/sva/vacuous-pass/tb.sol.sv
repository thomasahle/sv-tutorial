module tb;
  logic clk = 0, rst_n = 0;
  logic req = 0, gnt = 0;

  always #5 clk = ~clk;

  vacuous_demo dut(.clk, .rst_n, .req, .gnt);

  initial begin
    @(posedge clk); rst_n = 1;
    repeat(3) @(posedge clk);
    req = 1; @(posedge clk); req = 0;        // $rose(req) fires here
    @(posedge clk); gnt = 1; @(posedge clk); gnt = 0;  // gnt within 2 cycles — property passes
    repeat (4) @(posedge clk);
    $display("done: rg_cover should have fired.");
    $finish;
  end
endmodule
