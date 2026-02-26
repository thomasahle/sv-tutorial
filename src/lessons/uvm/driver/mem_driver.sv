import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_driver extends uvm_driver #(mem_item);
  `uvm_component_utils(mem_driver)
  virtual mem_if vif;
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // TODO: retrieve the virtual interface from config_db
    //       type: virtual mem_if, key: "vif"
    //       if the get() fails, call `uvm_fatal("NOVIF", "Virtual interface not found")
  endfunction
  task run_phase(uvm_phase phase);
    mem_item req;
    forever begin
      seq_item_port.get_next_item(req);
      // TODO: wait for a rising clock edge
      // TODO: drive we, addr, and wdata onto the interface from the request item
      // TODO: wait one more rising clock edge (SRAM has 1-cycle read latency)
      // TODO: capture vif.rdata back into req.rdata
      seq_item_port.item_done();
    end
  endtask
endclass
