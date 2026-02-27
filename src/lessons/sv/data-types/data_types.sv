module top;
  // TODO: change to int (2-state signed 32-bit — used for loop counters in testbenches)
  bit [31:0] count;

  // TODO: change to logic [7:0] (4-state — RTL signals must propagate X to catch bugs)
  bit [7:0]  data;

  // TODO: add [4] after mem to make it an unpacked array of 4 bytes
  //       (right now mem is a scalar — mem[0] is just bit 0, not a full byte)
  logic [7:0] mem;

  int fail = 0;

  initial begin
    // A testbench counter must hold negative values
    count = -100;
    if (count < 0) $display("count = %0d  OK", count);
    else begin
      $display("FAIL count: %0d is not negative — use int, not bit [31:0]", count);
      fail++;
    end

    // An RTL signal must be able to hold the unknown value X
    data = 'x;
    if ($isunknown(data)) $display("data  = X     OK");
    else begin
      $display("FAIL data: 0x%02h is not X — use logic [7:0], not bit [7:0]", data);
      fail++;
    end

    // An unpacked array element must hold a full byte, not just one bit
    mem[0] = 8'hAB;
    mem[1] = 8'h12;
    if (mem[0] === 8'hAB && mem[1] === 8'h12) $display("mem[]  = {AB,12}  OK");
    else begin
      $display("FAIL mem: mem[0] is only 1 bit wide — add [4] after the name to make it an array");
      fail++;
    end

    if (fail == 0) $display("PASS");
    $finish;
  end
endmodule
