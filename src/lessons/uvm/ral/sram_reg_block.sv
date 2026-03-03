// TODO: change to extend uvm_reg instead; update super.new() to pass the register
//       width and coverage mode: super.new(name, 8, UVM_NO_COVERAGE)
class ctrl_reg extends uvm_object;
  `uvm_object_utils(ctrl_reg)
  // TODO: replace the two logic fields below with uvm_reg_field objects
  logic        enable = 0;   // bit 0
  logic [1:0]  mode   = 0;   // bits [2:1]
  localparam logic [3:0] ADDR = 4'h0;
  function new(string name = "ctrl_reg"); super.new(name); endfunction
  // TODO: add a virtual function void build(); create each field with
  //       uvm_reg_field::type_id::create(), then call .configure() to set its size and position
  // (the hand-rolled helpers below are replaced by uvm_reg's built-in .get() and .convert2string())
  function logic [7:0] to_data();  return {5'b0, mode, enable};  endfunction
  function string convert2string();
    return $sformatf("ctrl @ 0x%0h: enable=%0b mode=%0b (raw=0x%02h)", ADDR, enable, mode, to_data());
  endfunction
endclass

// TODO: change to extend uvm_reg_block instead; update super.new() to pass UVM_NO_COVERAGE
class sram_reg_block extends uvm_object;
  `uvm_object_utils(sram_reg_block)
  ctrl_reg ctrl;
  function new(string name = "sram_reg_block"); super.new(name); endfunction
  function void build();
    ctrl = ctrl_reg::type_id::create("ctrl");
    // TODO: call ctrl.build() then ctrl.configure(this) to register ctrl with this block
    // TODO: create the address map, add ctrl to it at offset 0, then call lock_model()
  endfunction
endclass
