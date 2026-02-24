// Testbench drives three req/gnt scenarios.
// With assertions active, scenario 2 triggers an assertion failure in the log.
module tb;
  logic clk = 0, req = 0, gnt = 0;

  always #5 clk = ~clk;

  monitor dut(.clk, .req, .gnt);

  initial begin
    @(posedge clk);

    // Scenario 1: valid grant — gnt arrives 2 cycles after req
    req = 1;
    @(posedge clk); req = 0;   // req high for 1 cycle; property starts
    @(posedge clk); gnt = 1;   // +1 cycle: no gnt yet
    @(posedge clk); gnt = 0;   // +2 cycles: gnt seen — property satisfied
    @(posedge clk);

    // Scenario 2: missing grant — 3 cycles pass with no gnt; assertion fires
    req = 1;
    @(posedge clk); req = 0;   // property starts
    @(posedge clk);            // +1: no gnt
    @(posedge clk);            // +2: no gnt
    @(posedge clk);            // +3: no gnt — assertion fires!
    @(posedge clk);

    // Scenario 3: back-to-back requests, each granted on the next cycle
    req = 1;
    @(posedge clk); req = 0; gnt = 1;   // property fires; gnt set
    @(posedge clk); req = 1; gnt = 0;   // first property satisfied; second starts
    @(posedge clk); req = 0; gnt = 1;   // second property satisfied
    @(posedge clk); gnt = 0;
    @(posedge clk);

    $finish;
  end
endmodule
