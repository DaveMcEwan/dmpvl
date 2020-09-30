`include "asrt.svh"
`include "dff.svh"

module corrCountLogdrop #(
  // Width of increment must be > 1 and <= TIME_W.
  parameter INCR_W = 16,

  // Defines precision of window function.
  parameter TIME_W = 8
) (
  input wire                i_clk,
  input wire                i_rst,
  input wire                i_cg,

  input  wire               i_x,
  input  wire               i_y,

  output wire [TIME_W+INCR_W-2:0]  o_countX,
  output wire [TIME_W+INCR_W-2:0]  o_countY,
  output wire [TIME_W+INCR_W-2:0]  o_countIsect,   // x AND y
  output wire [TIME_W+INCR_W-2:0]  o_countSymdiff, // x XOR y

  input  wire [$clog2(TIME_W+1)-1:0]  i_windowLengthExp,

  input  wire [TIME_W-1:0]  i_t,
  input  wire               i_zeroCounts // 1->Beginning of new window.
);

localparam COUNTER_W = TIME_W + INCR_W - 1;

wire [TIME_W-1:0] tScaledVec [TIME_W+1];
wire [INCR_W-1:0] incrVec [TIME_W+1];
wire [COUNTER_W-1:0] incrValueVec [TIME_W+1];
genvar i;
generate for (i = 0; i <= TIME_W; i=i+1) begin
  if (i == 0) begin
    assign tScaledVec[0] = '0;
    assign incrVec[0] = '0;
    assign incrValueVec[0] = '0;
  end else begin
    assign tScaledVec[i] = i_t << (TIME_W-i);

    logdropWindow #(
      .DATA_W         (INCR_W),
      .WINLEN         (1 << TIME_W),
      .ABSTRACT_MODEL (0)
    ) u_win (
      .i_t  (tScaledVec[i]),
      .i_x  ({ 1'b1, {INCR_W-1{1'b0}} }),
      .o_y  (incrVec[i])
    );

    assign incrValueVec[i] = { // (incrVec[i] << (TIME_W-i))
      {COUNTER_W-INCR_W-TIME_W+i{1'b0}},
      incrVec[i],
      {TIME_W-i{1'b0}}
    };
  end
end endgenerate

`dff_cg_norst(reg [COUNTER_W-1:0], incrValue, i_clk, i_cg)
always @* incrValue_d = incrValueVec[i_windowLengthExp];
`asrt(incrValue, i_clk, !i_rst && i_cg, $onehot0(incrValue_d))


`dff_cg_srst(reg [COUNTER_W-1:0], countX, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countX_d = i_x ?
  countX_q + incrValue_q :
  countX_q;

`dff_cg_srst(reg [COUNTER_W-1:0], countY, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countY_d = i_y ?
  countY_q + incrValue_q :
  countY_q;

`dff_cg_srst(reg [COUNTER_W-1:0], countIsect, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countIsect_d = (i_x & i_y) ?
  countIsect_q + incrValue_q :
  countIsect_q;

`dff_cg_srst(reg [COUNTER_W-1:0], countSymdiff, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countSymdiff_d = (i_x ^ i_y) ?
  countSymdiff_q + incrValue_q :
  countSymdiff_q;

assign o_countX       = countX_q;
assign o_countY       = countY_q;
assign o_countIsect   = countIsect_q;
assign o_countSymdiff = countSymdiff_q;

endmodule
