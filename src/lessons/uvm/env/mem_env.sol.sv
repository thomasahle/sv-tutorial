import uvm_pkg::*;
`include "uvm_macros.svh"

class mem_env extends uvm_env;
  `uvm_component_utils(mem_env)
  mem_agent      agent;
  mem_scoreboard scbd;
  mem_coverage   cov;
  function new(string name, uvm_component parent); super.new(name, parent); endfunction
  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    agent = mem_agent::type_id::create("agent", this);
    scbd  = mem_scoreboard::type_id::create("scbd",  this);
    cov   = mem_coverage::type_id::create("cov",   this);
  endfunction
  function void connect_phase(uvm_phase phase);
    agent.mon.ap.connect(scbd.analysis_export);
    agent.mon.ap.connect(cov.analysis_export);
  endfunction
endclass
