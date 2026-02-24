module fifo_checker(
  input logic clk,
  input logic wr_en, rd_en,
  input logic full, empty
);
  always @(posedge clk) begin
    // TODO: assert we never write when full
    // TODO: assert we never read when empty
  end
endmodule
