interface mem_if (input logic clk);
  logic        we;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;

  function string sprint();
    return $sformatf("we=%0b addr=%0h wdata=%0h rdata=%0h",
                     we, addr, wdata, rdata);
  endfunction

  // TODO: add modport initiator — testbench side: drives we/addr/wdata, reads clk and rdata
  // TODO: add modport target   — SRAM side: reads commands, drives rdata
endinterface
