
// Deassert o_rst 32 cycles after PLL is locked.
module fpgaReset (
  input  wire i_clk,
  input  wire i_pllLocked,
  output wire o_rst
);

reg [4:0] resetCounter_q = 5'd0;
reg reset_q = 1'b0;

// The odd style here forces synth tool to use a non-vector net for reset name.
always @(posedge i_clk)
  if (i_pllLocked && o_rst)
    {reset_q, resetCounter_q} <= resetCounter_q + 6'd1;

assign o_rst = !reset_q;

endmodule
