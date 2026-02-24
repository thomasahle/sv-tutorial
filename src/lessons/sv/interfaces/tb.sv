module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  adder_if bus(.clk(clk));         // interface instance holds all the shared signals
  adder    dut(.bus(bus));         // DUT connects through one interface port

  initial begin
    // Drive inputs via the interface's master side
    bus.a = 8'd10;  bus.b = 8'd20;
    @(posedge clk); #1;
    $display("10 + 20 = %0d  carry=%b (expect 30, carry=0)", bus.sum, bus.carry);

    // 200 + 100 = 300 overflows an 8-bit sum — carry should assert
    bus.a = 8'd200; bus.b = 8'd100;
    @(posedge clk); #1;
    $display("200 + 100 = %0d  carry=%b (expect 44, carry=1)", bus.sum, bus.carry);

    $finish;
  end
endmodule
