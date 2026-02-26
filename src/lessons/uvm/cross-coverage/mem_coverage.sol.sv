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
    addr_x_we: cross cp_addr, cp_we {
      ignore_bins no_write_reserved =
          binsof(cp_addr.addr) intersect {14, 15} &&
          binsof(cp_we.writes);
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
    `uvm_info("COV", $sformatf("Cross coverage: %.1f%%", pct), UVM_LOW)
    if (pct == 100.0)
      `uvm_info("COV", "PASS: all required addr × op bins hit", UVM_LOW)
    else
      `uvm_error("COV", $sformatf("FAIL: cross coverage only %.1f%% — some addr×op combinations not exercised", pct))
  endfunction
endclass
