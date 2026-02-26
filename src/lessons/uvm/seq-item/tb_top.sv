import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"

class item_test extends uvm_test;
  `uvm_component_utils(item_test)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    mem_item item = mem_item::type_id::create("item");
    int fail = 0;
    phase.raise_objection(this);

    // ── Check 1: read_c forces we=0 ───────────────────────────────────────────
    `uvm_info("TEST", "=== Check 1: read_c active — all operations should be reads ===", UVM_LOW)
    repeat (8) begin
      void'(item.randomize());
      `uvm_info("TEST", item.convert2string(), UVM_LOW)
      if (item.we !== 1'b0) begin
        `uvm_error("TEST", $sformatf("FAIL: we=%0b but read_c should force we=0", item.we))
        fail++;
      end
    end
    if (fail == 0) `uvm_info("TEST", "PASS: read_c held we=0 for all 8 items", UVM_LOW)

    // ── Check 2: disabling read_c allows writes ───────────────────────────────
    `uvm_info("TEST", "=== Check 2: read_c disabled — writes should appear ===", UVM_LOW)
    item.read_c.constraint_mode(0);
    begin
      int saw_write = 0;
      repeat (8) begin
        void'(item.randomize());
        `uvm_info("TEST", item.convert2string(), UVM_LOW)
        if (item.we === 1'b1) saw_write++;
      end
      if (saw_write > 0)
        `uvm_info("TEST", $sformatf("PASS: saw %0d write(s) with read_c off", saw_write), UVM_LOW)
      else
        `uvm_error("TEST", "FAIL: no writes seen after disabling read_c (extremely unlikely if constraint is off)")
    end

    phase.drop_objection(this);
  endtask
endclass

module tb_top;
  initial run_test("item_test");
endmodule
