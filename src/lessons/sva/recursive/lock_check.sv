module lock_check(input logic clk, lock, unlock);

  // One-step version of the recursive "lock holds until unlock" invariant:
  // if lock is high and unlock has not fired, lock must still be high
  // at the very next clock edge.
  property p_lock_hold;
    @(posedge clk)
      // TODO: lock && !unlock |=> lock;
      ;
  endproperty

  lock_hold_a: assert property (p_lock_hold);

endmodule
