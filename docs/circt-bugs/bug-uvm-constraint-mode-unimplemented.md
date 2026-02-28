# Bug: `constraint_mode(0)` and inline `randomize() with { }` do not work in circt-sim

## Summary

Two related SystemVerilog constraint-manipulation features are not implemented in circt-sim:

1. `obj.constraint_name.constraint_mode(0)` — disabling a named constraint at runtime
2. `void'(obj.randomize() with { ... })` — inline constraint override on an existing object

Both produce no effect: the original constraints remain active after the call, and the object
continues to randomize as if the call was never made.

## Reproduction

### Case 1: `constraint_mode(0)`

```systemverilog
class mem_item extends uvm_sequence_item;
  rand bit       we;
  rand logic [3:0] addr;
  constraint read_c { we == 0; }  // force reads by default
  ...
endclass

// In a test:
mem_item item = mem_item::type_id::create("item");

// With read_c active: all operations should be reads
repeat (8) begin
  void'(item.randomize());
  assert (item.we === 0);   // always holds — correct
end

// Disable read_c so writes can appear:
item.read_c.constraint_mode(0);
int saw_write = 0;
repeat (8) begin
  void'(item.randomize());
  if (item.we === 1) saw_write++;
end
// Expected: saw_write > 0 (with high probability)
// Actual:   saw_write == 0 — read_c is still active despite constraint_mode(0)
```

### Case 2: `randomize() with { }`

```systemverilog
// Force boundary addresses and writes:
void'(item.randomize() with { addr inside {0, 15}; we == 1; });
// Expected: item.addr in {0, 15} and item.we == 1
// Actual:   addr is unconstrained, we may be 0 — inline override has no effect
```

## Expected behavior

Per IEEE 1800-2017 §18.5.5, `constraint_mode(0)` disables the named constraint block for
subsequent `randomize()` calls until re-enabled. Per §18.5.11, `randomize() with { expr }`
adds an additional inline constraint for that single call.

Both are fundamental SV randomization features required by UVM constraint-based stimulus.

## Affected lessons

- `uvm/seq-item` — tests `item.read_c.constraint_mode(0)` to verify writes appear
- `uvm/constrained-random` — tests `item.weighted_c.constraint_mode(0)` and
  `item.randomize() with { addr inside {0,15}; we == 1; }`

## Additional notes

- Basic `void'(item.randomize())` with always-active constraints works correctly.
- The bug is in the circt-sim runtime's constraint solver / randomization engine,
  not in circt-verilog's compilation.

## Version

Tested with circt-sim from CIRCT commit `3f4e18c4b` (LLVM `aa3d6b37c`).
