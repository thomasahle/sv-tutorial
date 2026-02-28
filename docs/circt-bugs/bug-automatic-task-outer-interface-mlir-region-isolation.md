# Bug: Automatic task capturing outer-scope virtual interface generates invalid MLIR (region isolation violation)

## Summary

An `automatic` task defined in a module that references a module-level virtual interface variable
causes circt-verilog to emit an MLIR module that fails verification with
`'moore.read' op using value defined outside the region`.
The compiler itself reports: `generated MLIR module failed to verify; this is likely a bug in circt-verilog`.

## Reproduction

```systemverilog
// mem_if.sv
interface mem_if (input logic clk);
  logic        we;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;
endinterface

// tb.sv
module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  mem_if vif(.clk(clk));   // <— module-scope interface instance

  // sram DUT connected via the interface
  sram dut(
    .clk   (vif.clk),
    .we    (vif.we),
    .addr  (vif.addr),
    .wdata (vif.wdata),
    .rdata (vif.rdata)
  );

  // Automatic task that captures the outer `vif` reference
  task automatic write_word(input logic [3:0] a, input logic [7:0] data);
    vif.we = 1; vif.addr = a; vif.wdata = data;   // <— uses outer `vif`
    @(posedge vif.clk); #1;
    vif.we = 0;
  endtask

  task automatic read_word(input  logic [3:0] a, output logic [7:0] data);
    vif.addr = a;
    @(posedge vif.clk); #1;
    data = vif.rdata;
  endtask

  initial begin
    logic [7:0] result;
    write_word(4'd5, 8'd42);
    read_word (4'd5, result);
    if (result === 8'd42) $display("PASS");
    else                  $display("FAIL: got %0d", result);
    $finish;
  end
endmodule
```

```
$ circt-verilog --ir-llhd --timescale 1ns/1ns --single-unit -o out.mlir tb.sv sram.sv mem_if.sv
tb.sv:27:5: error: 'moore.read' op using value defined outside the region
    vif.we = 1; vif.addr = a; vif.wdata = data;
    ^
note: see current operation: %0 = "moore.read"(<<UNKNOWN SSA VALUE>>)
tb.sv:26:18: note: required by region isolation constraints
  task automatic write_word(input logic [3:0] a, input logic [7:0] data);
                 ^
tb.sv:33:18: error: 'moore.read' op using value defined outside the region
  task automatic read_word(input  logic [3:0] a, output logic [7:0] data);
                 ^
generated MLIR module failed to verify; this is likely a bug in circt-verilog
```

## Expected behavior

Per IEEE 1800-2017 §13.4.2, automatic tasks may freely reference variables in their enclosing
scope (including interface instances declared in the containing module). The lowering to MLIR
must not create region-isolated SSA regions that disallow upward references to module-level
values.

The task body should either:
- receive `vif` as an implicit argument passed by the caller, or
- be lowered outside the isolated region so that the module-level SSA value is in scope.

Slang (the reference front-end) elaborates this correctly.

## Workaround

None known at the MLIR level. Rewriting tasks as non-`automatic` changes semantics (no
re-entrant stack frame) and does not fix the verification error. Moving task bodies into
dedicated modules is not idiomatic SV.

## Additional notes

- Non-`automatic` tasks with the same interface accesses do not trigger this error.
- The crash is triggered solely by the `automatic` keyword combined with interface access via a
  module-scope variable; removing `automatic` (accepting non-reentrant semantics) suppresses it.
- The `<<UNKNOWN SSA VALUE>>` in the diagnostic is itself a sign that the value lookup has
  already failed inside the region, making the error message somewhat opaque.

## Version

Tested with circt-verilog from CIRCT commit `3f4e18c4b` (LLVM `aa3d6b37c`).

## Status: FIXED (compile crash)

**Fixed by:** `35fedd92a [ImportVerilog] Capture outer interface refs in tasks`

The MLIR region-isolation crash is resolved. `circt-verilog` now compiles this pattern successfully.

**New issue:** The simulation still hangs — see GitHub issue #8. The root cause is different: `moore.wait_event` inside a `func.func` (the lowered task body) reads `vif.clk` from the LLVM backing store rather than from an LLHD signal, so the LLHD scheduler never wakes the suspended process on a clock edge.
