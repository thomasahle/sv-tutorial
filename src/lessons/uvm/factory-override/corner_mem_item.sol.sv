import uvm_pkg::*;
`include "uvm_macros.svh"

class corner_mem_item extends mem_item;
  `uvm_object_utils(corner_mem_item)

  // Override range_c to target only boundary addresses (0 and 15)
  constraint range_c { addr inside {0, 15}; }

  function new(string name = "corner_mem_item"); super.new(name); endfunction
endclass
