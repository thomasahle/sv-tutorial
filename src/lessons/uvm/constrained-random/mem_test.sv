import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_test extends uvm_test;
  `uvm_component_utils(mem_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction

  task run_phase(uvm_phase phase);
    mem_item item = mem_item::type_id::create("item");
    phase.raise_objection(this);

    // ── Scenario 1: default weighted distribution ─────────────────────────────
    `uvm_info("TEST", "=== Scenario 1: weighted_c active ===", UVM_LOW)
    repeat (4) begin
      void'(item.randomize());
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
    end

    // ── Scenario 2: inline override — force boundary writes ───────────────────
    // TODO: use randomize() with { ... } to force writes (we==1) to boundary addresses (0 and 15)
    `uvm_info("TEST", "=== Scenario 2: inline override (boundary writes only) ===", UVM_LOW)
    repeat (4) begin
      void'(item.randomize());  // replace with randomize() with { ... }
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
      if (!(item.addr inside {0, 15}) || item.we !== 1'b1)
        `uvm_error("TEST", $sformatf("FAIL: expected boundary write, got addr=%0d we=%0b", item.addr, item.we))
    end

    // ── Scenario 3: constraint_mode off — uniform distribution ────────────────
    // TODO: call constraint_mode(0) on weighted_c to disable it
    `uvm_info("TEST", "=== Scenario 3: weighted_c disabled ===", UVM_LOW)
    begin
      int interior = 0;
      repeat (16) begin
        void'(item.randomize());
        `uvm_info("TEST", item.convert2string(), UVM_LOW)
        if (item.addr inside {[1:14]}) interior++;
      end
      if (interior > 0)
        `uvm_info("TEST", $sformatf("PASS: %0d/16 items hit interior addresses (uniform spread)", interior), UVM_LOW)
      else
        `uvm_error("TEST", "FAIL: no interior addresses seen — weighted_c may still be active")
    end

    phase.drop_objection(this);
  endtask
endclass
