// Testbench for sram_core.
// Writes three values to different addresses, then reads them back.
// Registered reads have 1-cycle latency: drive addr on cycle N,
// rdata reflects that address on cycle N+1.
module tb;
  logic       clk = 0;   // driven by clock generator below
  logic       we  = 0;   // write-enable
  logic [3:0] addr  = 0; // byte address (0..15)
  logic [7:0] wdata = 0; // data to write
  logic [7:0] rdata;     // data read out — valid 1 cycle after addr

  int fail = 0;

  // Clock generator: period = 10 time units
  always #5 clk = ~clk;

  // Connect all ports by name (shorthand: .port matches variable of same name)
  sram_core dut(.*);

  initial begin
    // Write addr=2, data=42
    we = 1; addr = 4'd2; wdata = 8'd42;
    @(posedge clk); #1; we = 0;

    // Write addr=7, data=99
    we = 1; addr = 4'd7; wdata = 8'd99;
    @(posedge clk); #1; we = 0;

    // Write addr=0, data=13
    we = 1; addr = 4'd0; wdata = 8'd13;
    @(posedge clk); #1; we = 0;

    // Read and check each address (1-cycle read latency)
    addr = 4'd2; @(posedge clk); #1;
    if (rdata === 8'd42)
      $display("PASS  mem[2] = %0d", rdata);
    else begin
      $display("FAIL  mem[2] = %0d  (expected 42)", rdata);
      fail++;
    end

    addr = 4'd7; @(posedge clk); #1;
    if (rdata === 8'd99)
      $display("PASS  mem[7] = %0d", rdata);
    else begin
      $display("FAIL  mem[7] = %0d  (expected 99)", rdata);
      fail++;
    end

    addr = 4'd0; @(posedge clk); #1;
    if (rdata === 8'd13)
      $display("PASS  mem[0] = %0d", rdata);
    else begin
      $display("FAIL  mem[0] = %0d  (expected 13)", rdata);
      fail++;
    end

    if (fail == 0) $display("PASS");
    $finish;
  end
endmodule
