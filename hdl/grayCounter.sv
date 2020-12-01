`include "dff.svh"

module grayCounter #(
  parameter WIDTH = 8,  // >= 2

  // 0 -> gray-to-bin-inc-to-gray in single cycle.
  // 1 -> bin-inc and bin-to-gray separate FFs
  //      with result 1-cycle later.
  parameter FAST_NOT_SMALL = 0
) (
  input  wire                         i_clk,
  input  wire                         i_rst, // zero-counter
  input  wire                         i_cg,

  input  wire                         i_incr, // increment-counter
  output wire [WIDTH-1:0]             o_gray
);

genvar i;

`dff_cg_srst(reg [WIDTH-1:0], gray, i_clk, i_cg, i_rst, '0)
assign o_gray = gray_q;

generate if (FAST_NOT_SMALL) begin : fastNotSmall

  `dff_cg_srst(reg [WIDTH-1:0], binCntr, i_clk, i_cg, i_rst, '0)
  always @* binCntr_d = i_incr ? (binCntr_q + 'd1) : binCntr_q;

  always @* gray_d = (binCntr_d >> 1) ^ binCntr_d;

end : fastNotSmall else begin : smallNotFast

  wire [WIDTH-1:0] binCntr;
  for (i = 0; i < WIDTH; i=i+1) begin
    assign binCntr[i] = ^(gray_q >> i);
  end

  wire [WIDTH-1:0] binCntr_plus1 = binCntr + 'd1;

  always @* gray_d = i_incr ? ((binCntr_plus1 >> 1) ^ binCntr_plus1) : gray_q;

end : smallNotFast endgenerate

endmodule
