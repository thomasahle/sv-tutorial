module sram_check (
  input  logic        clk, we,
  input  logic [3:0]  addr,
  input  logic [7:0]  wdata,
  output logic [7:0]  rdata
);

  // Inline SRAM model with combinational read
  logic [7:0] mem [0:15];
  always_ff @(posedge clk) if (we) mem[addr] <= wdata;
  assign rdata = mem[addr];

  // Named sequences with formal arguments act like reusable templates.
  // Each formal argument ('a', 'd') is replaced with the actual value
  // supplied at every call site.

  sequence write_txn(logic [3:0] a, logic [7:0] d);
    // TODO: we is high AND addr equals a AND wdata equals d
  endsequence

  // After write_txn fires, one cycle later: if addr still equals a,
  // rdata must equal d.
  property wr_rd_p(logic [3:0] a, logic [7:0] d);
    @(posedge clk) write_txn(a, d) |=> (addr == a) |-> (rdata == d);
  endproperty

  // TODO: assert wr_rd_p for two address/data scenarios:
  //   addr0_check:  address 4'd0,  data 8'hA5
  //   addr15_check: address 4'hF,  data 8'hFF

endmodule
