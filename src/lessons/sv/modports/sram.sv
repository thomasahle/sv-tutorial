module sram (mem_if.target bus);
  logic [7:0] mem [0:15];

  always_ff @(posedge bus.clk) begin
    if (bus.we) mem[bus.addr] <= bus.wdata;
    bus.rdata <= mem[bus.addr];
  end
endmodule
