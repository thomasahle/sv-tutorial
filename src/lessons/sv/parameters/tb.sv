module tb;
  logic       clk=0, rst_n=0, en=1;
  logic [7:0] cnt8;

  always #5 clk = ~clk;

  // No parameter override — uses the default N=8
  counter_n dut(.clk, .rst_n, .en, .count(cnt8));

  initial begin
    @(posedge clk); rst_n=1;
    repeat(5) @(posedge clk);
    #1 $display("after 5 cycles: %0d (expect 5)", cnt8);
    $finish;
  end
endmodule
