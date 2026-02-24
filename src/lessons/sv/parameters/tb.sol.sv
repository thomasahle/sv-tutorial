module tb;
  logic       clk=0, rst_n=0, en=1;
  logic [3:0] cnt4;
  logic [7:0] cnt8;

  always #5 clk = ~clk;

  // Two instances at different widths — both share the same clock and reset
  counter_n #(.N(4)) u4(.clk, .rst_n, .en, .count(cnt4));
  counter_n #(.N(8)) u8(.clk, .rst_n, .en, .count(cnt8));

  initial begin
    @(posedge clk); rst_n=1;
    // After 20 cycles: the 4-bit counter wraps at 16, landing at 4 (20 mod 16)
    repeat(20) @(posedge clk);
    #1 $display("4-bit wraps at 16: %0d (expect 4)", cnt4);
    $display("8-bit count:        %0d (expect 20)", cnt8);
    $finish;
  end
endmodule
