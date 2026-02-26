import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"
`include "mem_driver.sv"
`include "mem_seq.sv"

class seq_test extends uvm_test;
  `uvm_component_utils(seq_test)
  uvm_sequencer #(mem_item) seqr;
  mem_driver                drv;

  function new(string name, uvm_component parent); super.new(name, parent); endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    seqr = uvm_sequencer #(mem_item)::type_id::create("seqr", this);
    drv  = mem_driver::type_id::create("drv",  this);
  endfunction

  function void connect_phase(uvm_phase phase);
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction

  task run_phase(uvm_phase phase);
    mem_seq seq = mem_seq::type_id::create("seq");
    phase.raise_objection(this);
    seq.start(seqr);
    if (drv.received == seq.num_items)
      `uvm_info("TEST", $sformatf("PASS: driver received all %0d items", drv.received), UVM_LOW)
    else
      `uvm_error("TEST", $sformatf("FAIL: expected %0d items, driver received %0d", seq.num_items, drv.received))
    phase.drop_objection(this);
  endtask
endclass

module tb_top;
  initial run_test("seq_test");
endmodule
