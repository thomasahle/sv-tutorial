# Bug: UVM run_phase cleanup hangs when a driver uses a `forever` loop; `set_type_override` has no effect

## Summary

Two related UVM infrastructure issues in circt-sim:

1. **Phase cleanup hang**: After all objections are dropped in `run_phase`, circt-sim cannot
   terminate concurrent `run_phase` tasks that contain `forever` loops (the standard UVM driver
   pattern). The simulation advances time but `run_test()` never returns, causing the testbench's
   post-run-test code to never execute.

2. **Factory override not applied**: `mem_item::type_id::set_type_override(corner_mem_item::get_type())`
   registers a factory override, but subsequent `mem_item::type_id::create("item")` calls return
   a plain `mem_item` instead of the overriding `corner_mem_item` type.

## Reproduction

### Issue 1: Phase cleanup hang

```systemverilog
// Driver with standard forever-loop pattern
class mem_driver extends uvm_driver #(mem_item);
  task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);   // blocks when no items remain
      // ... drive DUT ...
      seq_item_port.item_done();
    end
  endtask
endclass

// Test that runs a sequence then drops objection
class seq_test extends uvm_test;
  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    seq.start(seqr);           // sends N items; driver processes all N
    phase.drop_objection(this); // UVM should now end run_phase
  endtask
endclass

module tb_top;
  initial begin
    run_test("seq_test");
    // Expected: run_test() returns here after phases complete
    if (uvm_report_server::get_server().get_severity_count(UVM_ERROR) == 0)
      $display("PASS");
  end
endmodule
```

**Observed**: After `phase.drop_objection(this)`, circt-sim advances simulation time but
`run_test()` never returns. With `--max-time 10000000` (10 ns), the simulator reports:

```
[circt-sim] Main loop exit: maxTime reached (10000000 >= 10000000 fs), iter=21
```

The driver's `forever` loop (blocked in `get_next_item`) prevents the UVM phase manager from
completing cleanup. In compliant UVM simulators, the phase manager forcibly terminates all
`run_phase` processes when the last objection is dropped.

### Issue 2: Factory override not applied

```systemverilog
class corner_mem_item extends mem_item;
  `uvm_object_utils(corner_mem_item)
  constraint range_c { addr inside {0, 15}; }  // only boundary addresses
  ...
endclass

class mem_test_corner extends uvm_test;
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    mem_item::type_id::set_type_override(corner_mem_item::get_type());
  endfunction

  task run_phase(uvm_phase phase);
    phase.raise_objection(this);
    repeat (4) begin
      mem_item item = mem_item::type_id::create("item");
      // Expected: item is a corner_mem_item — addr in {0, 15}
      // Actual:   item is a plain mem_item — addr is unconstrained (1, 7, 11, ...)
      void'(item.randomize());
    end
    phase.drop_objection(this);
  endtask
endclass
```

**Observed**: Items created after the override are plain `mem_item` objects with unconstrained
addresses, not `corner_mem_item` objects with the boundary constraint.

## Expected behavior

1. Per IEEE 1800-2017 §9.3.2 and UVM LRM §8.3, when all objections are dropped and the phase
   manager ends `run_phase`, all concurrent processes in that phase should be killed (forked
   processes are automatically reaped). `run_test()` must return to allow post-test code to run.

2. Per UVM LRM §8.2.2, after `set_type_override(T)`, any `create()` call on the overridden
   type should return an object of type `T`.

## Affected lessons

- `uvm/sequence` — driver's `forever` loop prevents `run_test()` from returning
- `uvm/factory-override` — factory override not applied

## Version

Tested with circt-sim from CIRCT commit `3f4e18c4b` (LLVM `aa3d6b37c`).
