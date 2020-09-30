`include "dff.svh"

module edgeDetect (
  input  wire i_clk,
  input  wire i_x,
  output wire o_rise,
  output wire o_fall,
  output wire o_either
);

`dff_nocg_norst(reg, x, i_clk)
always @* x_d = i_x;

assign o_rise = i_x && !x_q;
assign o_fall = !i_x && x_q;
assign o_either = o_rise || o_fall;

endmodule
