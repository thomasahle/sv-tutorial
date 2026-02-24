module bus_check(input logic clk, valid, ready, done);

  property p_transfer;
    @(posedge clk) valid |-> (valid[*4]) intersect (ready[*4]);
  endproperty

  property p_complete;
    @(posedge clk) valid |-> (##[1:4] ready) and (##[1:8] done);
  endproperty

  transfer_a: assert property (p_transfer);
  complete_a: assert property (p_complete);

endmodule
