import uvm_pkg::*;
`include "uvm_macros.svh"

// Logging stub: receives each item from the sequencer and prints it.
// No DUT connection needed — this lesson is about the sequence handshake.
class mem_driver extends uvm_driver #(mem_item);
  `uvm_component_utils(mem_driver)
  int unsigned received = 0;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  task run_phase(uvm_phase phase);
    mem_item req;
    forever begin
      seq_item_port.get_next_item(req);
      received++;
      `uvm_info("DRV", $sformatf("[%0d] %s", received, req.convert2string()), UVM_LOW)
      seq_item_port.item_done();
    end
  endtask
endclass
