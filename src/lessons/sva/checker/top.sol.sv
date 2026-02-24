module handshake_check(input logic clk, req, ack);
  property p;
    @(posedge clk) req |=> ##[1:3] ack;
  endproperty
  req_ack_a: assert property (p);
endmodule

module top(input logic clk,
           input logic req1, ack1,
           input logic req2, ack2);

  handshake_check c1(clk, req1, ack1);
  handshake_check c2(clk, req2, ack2);

endmodule
