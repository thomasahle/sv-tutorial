module implication(input logic clk, req, ack);

  // Overlapping: ack must be high THE SAME cycle req is high
  property p_ol;
    // TODO: @(posedge clk) req |-> ack;
  endproperty

  // Non-overlapping: ack must be high the NEXT cycle after req
  property p_nol;
    // TODO: @(posedge clk) req |=> ack;
  endproperty

  a_ol:  assert property (p_ol);
  a_nol: assert property (p_nol);

endmodule
