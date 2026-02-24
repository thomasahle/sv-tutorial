module tb;
  logic clk=0, rst_n=0, d=0, q;

  always #5 clk = ~clk;            // 10-unit clock period

  dff dut(.clk, .rst_n, .d, .q);

  initial begin
    // rst_n starts low — q should be 0 regardless of d
    @(posedge clk); #1;
    $display("in reset:    q=%b (expect 0)", q);

    // Release reset and present d=1; q follows on the next rising edge
    rst_n=1; d=1; @(posedge clk); #1;
    $display("d=1 clocked: q=%b (expect 1)", q);

    // Lower d; q should update to 0 on the next edge
    d=0; @(posedge clk); #1;
    $display("d=0 clocked: q=%b (expect 0)", q);
    $finish;
  end
endmodule
