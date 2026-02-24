module tb;
  logic clk = 0, rst_n;
  logic [7:0] data;

  xcheck dut(.clk(clk), .rst_n(rst_n), .data(data));

  always #5 clk = ~clk;

  initial begin
    rst_n = 0; data = 8'h00;
    @(posedge clk); #1;
    rst_n = 1;
    @(posedge clk); #1; data = 8'hA5; // normal value
    @(posedge clk); #1; data = 8'hFF;
    @(posedge clk); #1; data = 'x;    // X value — assertion fires here
    @(posedge clk); #1;
    @(posedge clk); #1;
    $finish;
  end
endmodule
