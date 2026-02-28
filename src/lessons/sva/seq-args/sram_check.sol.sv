module sram_check (
  input  logic        clk, we,
  input  logic [3:0]  addr,
  input  logic [7:0]  wdata,
  output logic [7:0]  rdata
);

  logic [7:0] mem [0:15];
  always_ff @(posedge clk) if (we) mem[addr] <= wdata;
  assign rdata = mem[addr];

  sequence write_txn(logic [3:0] a, logic [7:0] d);
    we && (addr == a) && (wdata == d)
  endsequence

  property wr_rd_p(logic [3:0] a, logic [7:0] d);
    @(posedge clk) write_txn(a, d) |=> (addr == a) |-> (rdata == d);
  endproperty

  addr0_check:  assert property (wr_rd_p(4'd0, 8'hA5));
  addr15_check: assert property (wr_rd_p(4'hF, 8'hFF));

endmodule
