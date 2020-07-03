`include "dff.vh"

module corrCountRect #(
  // Should be larger than TIME_W by a "few" bits to get usable resolution.
  // Must be at least twice TIME_W for full resolution.
  parameter DATA_W = 16,

  // Defines precision of window function.
  parameter TIME_W = 8
) (
  input wire                i_clk,
  input wire                i_rst,
  input wire                i_cg,

  input  wire               i_x,
  input  wire               i_y,

  output wire [DATA_W-1:0]  o_countX,
  output wire [DATA_W-1:0]  o_countY,
  output wire [DATA_W-1:0]  o_countIsect,   // x AND y
  output wire [DATA_W-1:0]  o_countSymdiff, // x XOR y

  input  wire [$clog2(TIME_W+1)-1:0]  i_windowLengthExp,

  input  wire               i_zeroCounts // 1->Beginning of new window.
);

wire [DATA_W-TIME_W-1:0] maxIncr = {DATA_W-TIME_W{1'b1}};
wire [DATA_W-TIME_W-1:0] incrValueNarrowVec [TIME_W+1];
genvar i;
generate for (i = 0; i <= TIME_W; i=i+1) begin
  if (i == 0) begin
    assign incrValueNarrowVec[0] = maxIncr;
  end else begin
    assign incrValueNarrowVec[i] = maxIncr >> (i-1);
  end
end endgenerate
`dff_cg_norst(reg [DATA_W-TIME_W-1:0], incrValueNarrow, i_clk, i_cg)
always @* incrValueNarrow_d = incrValueNarrowVec[i_windowLengthExp];

reg [DATA_W-1:0] incrValue;
always @* begin
  incrValue = '0;
  incrValue[DATA_W-TIME_W-1:0] = incrValue[DATA_W-TIME_W-1:0] | incrValueNarrow_q;
end

`dff_cg_srst(reg [DATA_W-1:0], countX, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countX_d = i_x ? countX_q + incrValue : countX_q;

`dff_cg_srst(reg [DATA_W-1:0], countY, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countY_d = i_y ? countY_q + incrValue : countY_q;

`dff_cg_srst(reg [DATA_W-1:0], countIsect, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countIsect_d = (i_x & i_y) ? countIsect_q + incrValue : countIsect_q;

`dff_cg_srst(reg [DATA_W-1:0], countSymdiff, i_clk, i_cg, i_rst || i_zeroCounts, '0)
always @* countSymdiff_d = (i_x ^ i_y) ? countSymdiff_q + incrValue : countSymdiff_q;

assign o_countX       = countX_q;
assign o_countY       = countY_q;
assign o_countIsect   = countIsect_q;
assign o_countSymdiff = countSymdiff_q;

endmodule
