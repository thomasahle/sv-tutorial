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
    if (!uvm_config_db #(virtual mem_if)::get(this, "", "vif", vif))
      `uvm_fatal("NOVIF", "Virtual interface not found")
  endfunction
  task run_phase(uvm_phase phase);
    mem_item req;
    forever begin
      seq_item_port.get_next_item(req);
      @(posedge vif.clk);
      vif.we    <= req.we;
      vif.addr  <= req.addr;
      vif.wdata <= req.wdata;
      @(posedge vif.clk);
      req.rdata = vif.rdata;
      `uvm_info("DRV", $sformatf("drove %s → rdata=%0d", req.convert2string(), req.rdata), UVM_MEDIUM)
      seq_item_port.item_done();
    end
  endtask
endclass
