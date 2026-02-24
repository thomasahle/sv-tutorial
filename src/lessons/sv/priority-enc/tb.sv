module tb;
  logic [3:0] req;
  logic [1:0] grant;
  logic       valid;

  // Instantiate the design under test, connecting ports by name
  priority_enc dut(.req, .grant, .valid);

  initial begin
    // No requests: valid stays low
    req=4'b0000; #1 $display("req=%b → grant=%0d valid=%b (expect valid=0)", req, grant, valid);
    // Only bit 0 set: grant=0
    req=4'b0001; #1 $display("req=%b → grant=%0d valid=%b (expect grant=0)", req, grant, valid);
    // Bits 1 and 2 both set: higher-index bit 2 wins
    req=4'b0110; #1 $display("req=%b → grant=%0d valid=%b (expect grant=2)", req, grant, valid);
    // Bits 1 and 3 both set: highest bit 3 wins
    req=4'b1010; #1 $display("req=%b → grant=%0d valid=%b (expect grant=3)", req, grant, valid);
  end
endmodule
