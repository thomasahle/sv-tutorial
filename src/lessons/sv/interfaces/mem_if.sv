// Bundle all SRAM signals into one reusable port.
interface mem_if (input logic clk);
  logic        we;
  logic [3:0]  addr;
  logic [7:0]  wdata;
  logic [7:0]  rdata;

  // TODO: implement sprint() — return a formatted string showing the current
  //       signal values (we, addr, wdata, rdata) using $sformatf
endinterface
