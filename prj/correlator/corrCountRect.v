`include "asrt.svh"
`include "dff.svh"

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

  input  wire [$clog2(TIME_W+1)-1:0]  i_windowLengthExp,

  input  wire               i_zeroCounts // 1->Beginning of new window.
);

wire [TIME_W-1:0] incrValueVec [TIME_W+1];
genvar i;
generate for (i = 0; i <= TIME_W; i=i+1) begin
  if (i == 0) begin
    assign incrValueVec[0] = '0;
  end else begin
    assign incrValueVec[i] = (1 << (TIME_W-i));
  end
end endgenerate

`dff_cg_norst(reg [TIME_W-1:0], incrValue, i_clk, i_cg)
always @* incrValue_d = incrValueVec[i_windowLengthExp];
`asrt(incrValue, i_clk, !i_rst && i_cg, $onehot0(incrValue_d))

`dff_cg_srst(reg [TIME_W-1:0], countX, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countX_d = i_x ?
  countX_q + incrValue_q :
  countX_q;

`dff_cg_srst(reg [TIME_W-1:0], countY, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countY_d = i_y ?
  countY_q + incrValue_q :
  countY_q;

`dff_cg_srst(reg [TIME_W-1:0], countIsect, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countIsect_d = (i_x & i_y) ?
  countIsect_q + incrValue_q :
  countIsect_q;
`asrt(isectLeX, i_clk, !i_rst && i_cg && (incrValue_q != '0), countX_q >= countIsect_q)
`asrt(isectLeY, i_clk, !i_rst && i_cg && (incrValue_q != '0), countY_q >= countIsect_q)

`dff_cg_srst(reg [TIME_W-1:0], countSymdiff, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countSymdiff_d = (i_x ^ i_y) ?
  countSymdiff_q + incrValue_q :
  countSymdiff_q;

assign o_countX       = countX_q;
assign o_countY       = countY_q;
assign o_countIsect   = countIsect_q;
assign o_countSymdiff = countSymdiff_q;

endmodule
