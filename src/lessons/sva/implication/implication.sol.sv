module implication(input logic clk, req, ack);

  property p_ol;
    @(posedge clk) req |-> ack;
  endproperty

  property p_nol;
    @(posedge clk) req |=> ack;
  endproperty

  a_ol:  assert property (p_ol);
  a_nol: assert property (p_nol);

endmodule
