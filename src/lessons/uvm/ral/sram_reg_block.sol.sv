class ctrl_reg extends uvm_reg;
  uvm_reg_field enable;
  uvm_reg_field mode;
  function new(string name = "ctrl_reg"); super.new(name, 8, UVM_NO_COVERAGE); endfunction
  virtual function void build();
    enable = uvm_reg_field::type_id::create("enable");
    enable.configure(this, 1, 0, "RW", 0, 0, 1, 0, 1);
    mode = uvm_reg_field::type_id::create("mode");
    mode.configure(this, 2, 1, "RW", 0, 0, 1, 0, 1);
  endfunction
  `uvm_object_utils(ctrl_reg)
endclass

class sram_reg_block extends uvm_reg_block;
  ctrl_reg ctrl;
  function new(string name = "sram_reg_block"); super.new(name, UVM_NO_COVERAGE); endfunction
  virtual function void build();
    ctrl = ctrl_reg::type_id::create("ctrl");
    ctrl.build();
    ctrl.configure(this);
    default_map = create_map("map", 'h0, 1, UVM_LITTLE_ENDIAN);
    default_map.add_reg(ctrl, 'h0, "RW");
    lock_model();
  endfunction
  `uvm_object_utils(sram_reg_block)
endclass
