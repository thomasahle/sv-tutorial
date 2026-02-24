module adder (
  input  logic [3:0] A, B,
  output logic [4:0] X
);
  always @(*) X = A + B;
endmodule
