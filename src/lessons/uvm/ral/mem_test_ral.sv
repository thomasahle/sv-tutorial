class mem_test_ral extends uvm_test;
  `uvm_component_utils(mem_test_ral)
  function new(string name, uvm_component parent); super.new(name, parent); endfunction

  task run_phase(uvm_phase phase);
    sram_reg_block ral;
    phase.raise_objection(this);
    ral = sram_reg_block::type_id::create("ral", this);
    ral.build();

    // Hand-rolled API: direct field assignment
    ral.ctrl.enable = 1;     // TODO: replace with .set(1) on the uvm_reg_field
    ral.ctrl.mode   = 2'b10; // TODO: replace with .set(2'b10) on the uvm_reg_field

    if (ral.ctrl.to_data() == 8'h05) // TODO: replace to_data() with .get(); update the strings below too
      `uvm_info("RAL_TEST", $sformatf("PASS: %s", ral.ctrl.convert2string()), UVM_NONE)
    else
      `uvm_error("RAL_TEST", $sformatf("FAIL: expected 0x05, got 0x%02h", ral.ctrl.to_data()))

    phase.drop_objection(this);
  endtask
endclass
