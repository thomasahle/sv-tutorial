# Bug: `virtual` interface field access in UVM class method crashes circt-verilog (MLIR region isolation)

## Summary

A UVM `uvm_driver` subclass that holds a `virtual mem_if vif` field and accesses it inside
`task run_phase` causes circt-verilog to crash with `Aborted()` (SIGABRT). The crash is an
assertion failure during MLIR verification — the same class of region-isolation violation seen
in the `automatic` task bug, but triggered inside a class method rather than a module-level task.

## Reproduction

```systemverilog
// mem_if.sv
interface mem_if (input logic clk);
  logic we; logic [3:0] addr; logic [7:0] wdata, rdata;
endinterface

// mem_driver.sv
import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_driver extends uvm_driver #(mem_item);
  `uvm_component_utils(mem_driver)
  virtual mem_if vif;           // <— virtual interface field

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db #(virtual mem_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found")
  endfunction

  task run_phase(uvm_phase phase);
    mem_item req;
    forever begin
      seq_item_port.get_next_item(req);
      @(posedge vif.clk);     // <— accesses vif inside class method
      vif.we    <= req.we;
      vif.addr  <= req.addr;
      seq_item_port.item_done();
    end
  endtask
endclass
```

```
$ circt-verilog --ir-llhd --timescale 1ns/1ns --single-unit \
    --uvm-path /path/to/uvm-core \
    -o out.mlir tb_top.sv mem_driver.sv mem_if.sv sram.sv ...
Aborted()
```

## Expected behavior

A `virtual interface` field in a UVM class that is accessed in a class method is valid
IEEE 1800-2017 SystemVerilog. The class method should be lowered so that the virtual interface
value (obtained from the UVM config DB at `build_phase`) is accessible to `run_phase`.

## Root cause hypothesis

circt-verilog lowers class methods into MLIR regions. The `vif` field is a reference to a
module-level signal value (the `mem_if` instance). When lowering `@(posedge vif.clk)`, the
compiler emits a `moore.read` on the virtual interface value, but the SSA value for `vif` is
defined outside the method's isolated MLIR region, triggering the same region-isolation
assertion that fires for `automatic` task captures (see
`bug-automatic-task-outer-interface-mlir-region-isolation.md`).

The `Aborted()` exit (SIGABRT) indicates an `assert()` failure in the CIRCT verification pass,
not a user-facing error.

## Affected UVM lessons

All lessons that use `virtual mem_if vif` in a class method:

- `uvm/driver` — `mem_driver` reads `vif.clk`, writes `vif.we/addr/wdata`, reads `vif.rdata`
- `uvm/env` — includes `mem_driver`
- `uvm/monitor` — `mem_monitor` reads `vif` signals in `run_phase`
- `uvm/coverage-driven` — includes `mem_driver` + `mem_monitor`
- `uvm/covergroup` — same
- `uvm/cross-coverage` — same

## Workaround

None known at the SV level. The pattern (`virtual if` field accessed in a class method) is
standard UVM idiom. Removing the `virtual` qualifier changes semantics entirely.

## Version

Tested with circt-verilog from CIRCT commit `3f4e18c4b` (LLVM `aa3d6b37c`).
