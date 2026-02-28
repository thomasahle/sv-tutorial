# Bug: `$bits()` on hierarchical reference to parameterized port fails with "unknown hierarchical name"

## Summary

`$bits(inst.port)` fails to resolve when the port's width is a parameter-dependent expression
(`$clog2(DEPTH)-1:0`). circt-verilog reports `unknown hierarchical name 'port'` and `no rvalue
generated for Variable`.

## Reproduction

```systemverilog
// sram.sv
module sram #(parameter int DEPTH = 16, parameter int WIDTH = 8) (
  input  logic                      clk,
  input  logic                      we,
  input  logic [$clog2(DEPTH)-1:0] addr,   // width is parameter-dependent
  input  logic [WIDTH-1:0]         wdata,
  output logic [WIDTH-1:0]         rdata
);
  logic [WIDTH-1:0] mem [0:DEPTH-1];
  always_ff @(posedge clk) begin
    if (we) mem[addr] <= wdata;
    rdata <= mem[addr];
  end
endmodule

// tb.sv
module tb;
  logic clk = 0;
  always #5 clk = ~clk;

  logic [2:0] addr4; logic [3:0] wdata4, rdata4; logic we4;
  sram #(.DEPTH(8), .WIDTH(4)) u_small(
    .clk, .we(we4), .addr(addr4), .wdata(wdata4), .rdata(rdata4));

  initial begin
    if ($bits(u_small.addr) !== 3) $display("FAIL");
    else                           $display("PASS");
    $finish;
  end
endmodule
```

```
$ circt-verilog --ir-llhd --timescale 1ns/1ns --single-unit -o out.mlir tb.sv sram.sv
tb.sv:9:15: error: unknown hierarchical name `addr`
    if ($bits(u_small.addr) !== 3) $display("FAIL");
              ^
sram.sv:4:36: note: no rvalue generated for Variable
  input  logic [$clog2(DEPTH)-1:0] addr,
                                   ^
```

## Expected behavior

`$bits(u_small.addr)` should return the elaborated bit-width of `addr` in the `u_small` instance,
which is `$clog2(8) = 3`. This is valid IEEE 1800-2017 §20.6.2 — `$bits` accepts a hierarchical
reference.

The same expression `$bits(addr4)` (referencing the connected net directly) works fine; the bug
is specific to the hierarchical path through a parameterized instance.

## Additional notes

- Removing the `$clog2(DEPTH)-1:0` dimension (making `addr` a fixed-width port) makes the
  hierarchical `$bits` work correctly.
- The error message "no rvalue generated for Variable" suggests the compiler is not fully
  elaborating parameterized port widths before resolving hierarchical references in `$bits`.
- Slang resolves this correctly.

## Version

Tested with circt-verilog from CIRCT commit `3f4e18c4b` (LLVM `aa3d6b37c`).
