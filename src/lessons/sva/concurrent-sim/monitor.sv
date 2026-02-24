module monitor(input logic clk, req, gnt);

  // When req goes high, gnt must follow within 1–3 cycles.
  property req_then_gnt;
    @(posedge clk)
      req |-> ##[1:3] gnt;
  endproperty

  // TODO: assert property (req_then_gnt)
  //         else $error("req was not followed by gnt within 3 cycles!");
  // TODO: cover property (req_then_gnt);

endmodule
