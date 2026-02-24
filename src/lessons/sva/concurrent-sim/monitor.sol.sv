module monitor(input logic clk, req, gnt);

  property req_then_gnt;
    @(posedge clk)
      req |-> ##[1:3] gnt;
  endproperty

  assert property (req_then_gnt)
    else $error("req was not followed by gnt within 3 cycles!");
  cover property (req_then_gnt);

endmodule
