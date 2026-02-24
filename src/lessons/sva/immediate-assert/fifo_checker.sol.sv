module fifo_checker(
  input logic clk,
  input logic wr_en, rd_en,
  input logic full, empty
);
  always @(posedge clk) begin
    assert (!wr_en || !full)
      else $error("Write to full FIFO!");
    assert (!rd_en || !empty)
      else $error("Read from empty FIFO!");
  end
endmodule
