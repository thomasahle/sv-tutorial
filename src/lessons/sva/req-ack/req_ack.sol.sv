module req_ack(input logic clk, req, ack);

  property req_ack_p;
    @(posedge clk) $rose(req) |=> ##[0:2] ack;
  endproperty

  req_ack_a: assert property (req_ack_p);

endmodule
