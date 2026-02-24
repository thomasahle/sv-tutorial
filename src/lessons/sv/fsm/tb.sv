module tb;
  logic clk=0, rst_n=0, din=0, detected;

  always #5 clk = ~clk;            // 10-unit clock period

  seq_det dut(.clk, .rst_n, .din, .detected);

  // Drive one bit per clock edge, then sample detected one unit after the edge
  task automatic send(input logic b);
    din = b; @(posedge clk); #1;
  endtask

  initial begin
    @(posedge clk); rst_n = 1;  // release reset

    // Send the target pattern 1→0→1
    send(1); send(0); send(1);
    $display("after 1-0-1:   detected=%b (expect 1)", detected);

    // A second match: the tail of ...0→1→0→1 ends with another 1-0-1
    send(0); send(1); send(0); send(1);
    $display("after 1-0-1:   detected=%b (expect 1)", detected);

    // Extra 0 breaks the pattern; detected should de-assert
    send(0);
    $display("after extra 0: detected=%b (expect 0)", detected);
    $finish;
  end
endmodule
