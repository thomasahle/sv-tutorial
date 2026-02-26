import uvm_pkg::*;
`include "uvm_macros.svh"

class corner_mem_item extends mem_item;
  // TODO: register this class with the UVM factory using `uvm_object_utils

  // TODO: override range_c so addr is constrained to only boundary addresses (0 and 15)
  //       the base class range_c keeps addr in [1:14]; this override replaces it

  function new(string name = "corner_mem_item"); super.new(name); endfunction
endclass
