// A checker is an encapsulated, reusable assertion block.
// (The tool represents it as a module; semantics are identical.)
module handshake_check(input logic clk, req, ack);
  property p;
    @(posedge clk)
      // TODO: req |=> ##[1:3] ack;
      ;
  endproperty
  req_ack_a: assert property (p);
endmodule

// Instantiate the checker for two independent channels
module top(input logic clk,
           input logic req1, ack1,
           input logic req2, ack2);

  handshake_check c1(clk, req1, ack1);
  handshake_check c2(clk, req2, ack2);

endmodule
