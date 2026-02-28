module tb;
  ctrl_state_t state;
  logic        reading, writing;

  int fail = 0;

  ctrl_display dut(.state, .reading, .writing);

  initial begin
    state = IDLE; #1;
    $display("%s IDLE:  reading=%b writing=%b",
             (reading===0 && writing===0) ? "PASS" : "FAIL", reading, writing);
    if (reading !== 0 || writing !== 0) fail++;

    state = READ; #1;
    $display("%s READ:  reading=%b writing=%b",
             (reading===1 && writing===0) ? "PASS" : "FAIL", reading, writing);
    if (reading !== 1 || writing !== 0) fail++;

    state = WRITE; #1;
    $display("%s WRITE: reading=%b writing=%b",
             (reading===0 && writing===1) ? "PASS" : "FAIL", reading, writing);
    if (reading !== 0 || writing !== 1) fail++;

    state = CMD; #1;
    $display("%s CMD:   reading=%b writing=%b",
             (reading===0 && writing===0) ? "PASS" : "FAIL", reading, writing);
    if (reading !== 0 || writing !== 0) fail++;

    if (fail == 0) $display("PASS");
    $finish;
  end
endmodule
