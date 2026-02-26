import uvm_pkg::*;
`include "uvm_macros.svh"
`include "mem_item.sv"
`include "mem_driver.sv"
`include "mem_monitor.sv"
`include "mem_scoreboard.sv"
`include "mem_coverage.sv"
`include "mem_agent.sv"
`include "mem_seq.sv"
`include "mem_env.sv"
`include "mem_test.sv"

module tb_top;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  logic clk = 0;
  always #5 clk = ~clk;
  mem_if mif(.clk(clk));
  sram dut(.clk(mif.clk), .we(mif.we), .addr(mif.addr), .wdata(mif.wdata), .rdata(mif.rdata));
  initial begin
    uvm_config_db #(virtual mem_if)::set(null, "uvm_test_top.*", "vif", mif);
    run_test("mem_test");
  end
endmodule
