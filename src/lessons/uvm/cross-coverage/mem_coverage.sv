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
    // TODO 1: add addr_x_we cross of cp_addr and cp_we
    // TODO 2: add ignore_bins to exclude writes to reserved addresses 14 and 15
    //         hint: binsof(cp_addr.addr) intersect {14, 15} && binsof(cp_we.writes)
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
    // TODO 3: print PASS if pct == 100.0; otherwise `uvm_error with the percentage
  endfunction
endclass
