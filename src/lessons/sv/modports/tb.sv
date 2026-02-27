module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  mem_if bus(.clk(clk));
  sram   dut(.bus(bus));

  int fail = 0;

  initial begin
    bus.we = 1; bus.addr = 4'd4; bus.wdata = 8'd88;
    @(posedge clk); #1;
    bus.we = 0;

    bus.addr = 4'd4; @(posedge clk); #1;
    $display("mem[4] = %0d (expect 88)", bus.rdata);
    if (bus.rdata !== 8'd88) fail++;

    bus.we = 1; bus.addr = 4'd11; bus.wdata = 8'd200;
    @(posedge clk); #1;
    bus.we = 0; bus.addr = 4'd11; @(posedge clk); #1;
    $display("mem[11] = %0d (expect 200)", bus.rdata);
    if (bus.rdata !== 8'd200) fail++;

    if (fail == 0) $display("PASS");
    $finish;
  end
endmodule
