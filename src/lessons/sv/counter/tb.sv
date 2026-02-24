module tb;
  logic       clk=0, rst_n=0, en=0;
  logic [7:0] count;

  always #5 clk = ~clk;            // 10-unit clock period

  counter dut(.clk, .rst_n, .en, .count);

  initial begin
    // Release reset and enable counting
    @(posedge clk); rst_n=1; en=1;
    repeat(5) @(posedge clk);
    #1 $display("after 5 cycles: %0d (expect 5)", count);

    // Disable the counter — count should hold
    en=0; @(posedge clk); #1;
    $display("after pause:    %0d (expect 5)", count);

    // Assert reset — count clears synchronously on the next edge
    rst_n=0; @(posedge clk); #1;
    $display("after reset:    %0d (expect 0)", count);
    $finish;
  end
endmodule
