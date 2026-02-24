module lock_check(input logic clk, lock, unlock);

  property p_lock_hold;
    @(posedge clk) lock && !unlock |=> lock;
  endproperty

  lock_hold_a: assert property (p_lock_hold);

endmodule
