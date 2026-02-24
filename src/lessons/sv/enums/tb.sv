module tb;
  status_t st;
  logic    active, err;

  // Instantiate the design under test, connecting ports by name
  status_display dut(.st, .active, .err);

  initial begin
    // Combinational: outputs update immediately after each assignment
    st = IDLE;    #1 $display("IDLE:    active=%b err=%b (expect 0 0)", active, err);
    st = RUNNING; #1 $display("RUNNING: active=%b err=%b (expect 1 0)", active, err);
    st = DONE;    #1 $display("DONE:    active=%b err=%b (expect 0 0)", active, err);
    st = ERROR;   #1 $display("ERROR:   active=%b err=%b (expect 0 1)", active, err);
  end
endmodule
