module tb;
  logic [7:0] a, b, sum;  // stimulus signals

  // Instantiate the design under test, connecting ports by name
  adder dut(.a(a), .b(b), .sum(sum));

  initial begin
    a = 8'd10; b = 8'd32;       // apply inputs
    #1 $display("sum = %0d", sum); // wait 1 time unit, then print result
  end
endmodule
