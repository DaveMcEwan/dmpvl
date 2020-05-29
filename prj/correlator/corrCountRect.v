`include "dff.vh"

module corrCountRect #(
  parameter TIME_W = 8
) (
  input wire                i_clk,
  input wire                i_rst,
  input wire                i_cg,

  input  wire               i_x,
  input  wire               i_y,

  output wire [TIME_W-1:0]  o_countX,
  output wire [TIME_W-1:0]  o_countY,
  output wire [TIME_W-1:0]  o_countIsect,   // x AND y
  output wire [TIME_W-1:0]  o_countSymdiff, // x XOR y

  input  wire               i_zeroCounts // 1->Beginning of new window.
);

wire incr_x = i_cg && i_x;
wire incr_y = i_cg && i_y;
wire incr_isect = i_cg && (i_x & i_y);
wire incr_symdiff = i_cg && (i_x ^ i_y);
wire zeroCount = i_rst || i_zeroCounts;
`dff_upcounter(reg [TIME_W-1:0], countX,        i_clk, incr_x,       zeroCount)
`dff_upcounter(reg [TIME_W-1:0], countY,        i_clk, incr_y,       zeroCount)
`dff_upcounter(reg [TIME_W-1:0], countIsect,    i_clk, incr_isect,   zeroCount)
`dff_upcounter(reg [TIME_W-1:0], countSymdiff,  i_clk, incr_symdiff, zeroCount)

assign o_countX       = countX_q;
assign o_countY       = countY_q;
assign o_countIsect   = countIsect_q;
assign o_countSymdiff = countSymdiff_q;

endmodule
