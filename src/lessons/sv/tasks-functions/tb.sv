module tb;
  logic clk = 0;
  logic [7:0] tx_data  = 0;
  logic       tx_valid = 0;

  always #5 clk = ~clk;

  // A function returns a value and cannot consume simulation time.
  // TODO: function automatic logic parity(input logic [7:0] d);
  //         return ^d;   // reduction XOR: 1 if an odd number of bits are set
  //       endfunction

  // A task can wait for clock edges (consume simulation time).
  // TODO: task automatic send(input logic [7:0] d);
  //         tx_data  = d;
  //         tx_valid = 1;
  //         @(posedge clk); #1;
  //         tx_valid = 0;
  //       endtask

  initial begin
    @(posedge clk); #1;
    send(8'h01);
    $display("sent 0x01  parity=%b (expect 1)", parity(8'h01));
    send(8'hFF);
    $display("sent 0xFF  parity=%b (expect 0)", parity(8'hFF));
    $finish;
  end
endmodule
