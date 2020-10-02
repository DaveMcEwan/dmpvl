module IBUFDS (
  input  wire I,
  input  wire IB,
  output reg O
);

always @(I or IB)
  if (I == 1'b1 && IB == 1'b0)
    O = 1'b1;
  else if (I == 1'b0 && IB == 1'b1)
    O = 1'b0;
`ifndef VERILATOR
  else if ((I == 1'bx) ||
           (I == 1'bz) ||
           (IB == 1'bx) ||
           (IB == 1'bz))
    O = 1'bx;
`endif

endmodule


