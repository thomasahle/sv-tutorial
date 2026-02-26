import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_coverage extends uvm_subscriber #(mem_item);
  `uvm_component_utils(mem_coverage)

  mem_item item;

  covergroup mem_cg;
    cp_addr: coverpoint item.addr {
      bins addr[] = {[0:15]};
    }
    cp_we: coverpoint item.we {
      bins reads  = {0};
      bins writes = {1};
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mem_cg = new();
  endfunction

  function void write(mem_item t);
    item = t;
    mem_cg.sample();
  endfunction

  function void report_phase(uvm_phase phase);
    real pct = mem_cg.get_coverage();
    `uvm_info("COV", $sformatf("Functional coverage: %.1f%%", pct), UVM_LOW)
    if (pct == 100.0)
      `uvm_info("COV", "PASS: all coverage bins hit", UVM_LOW)
    else
      `uvm_error("COV", $sformatf("FAIL: coverage only %.1f%% — some bins were not hit", pct))
  endfunction
endclass
