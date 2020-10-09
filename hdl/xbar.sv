`include "dff.svh"

// Crossbar convenience mux.
// For each output, select an input.
module xbar #(
  parameter N_IN = 5, // >= 2
  parameter N_OUT = 5, // >= 2
  parameter WIDTH = 8, // >= 1
  parameter FF_IN = 1,
  parameter FF_OUT = 1,
  parameter FF_SELECT = 1
) (
  input wire          i_clk,
  input wire          i_cg,

  input  wire [N_IN*WIDTH-1:0]          i_in,
  output wire [N_OUT*WIDTH-1:0]         o_out,

  input  wire [N_OUT*$clog2(N_IN)-1:0]  i_select
);

wire [N_IN*WIDTH-1:0] inFF;
generate if (FF_IN) begin
  `dff_cg_norst_d(reg [N_IN*WIDTH-1:0], inFF, i_clk, i_cg, i_in)
  assign inFF = inFF_q;
end else begin
  assign inFF = i_in;
end endgenerate

wire [N_OUT*$clog2(N_IN)-1:0] selectFF;
generate if (FF_IN) begin
  `dff_cg_norst_d(reg [N_OUT*$clog2(N_IN)-1:0], selectFF, i_clk, i_cg, i_select)
  assign selectFF = selectFF_q;
end else begin
  assign selectFF = i_select;
end endgenerate

wire [N_OUT*WIDTH-1:0] outFF;
generate if (FF_OUT) begin
  `dff_cg_norst_d(reg [N_OUT*WIDTH-1:0], outFF, i_clk, i_cg, outFF)
  assign o_out = outFF_q;
end else begin
  assign o_out = outFF;
end endgenerate

genvar i;
generate for (i = 0; i < N_OUT; i=i+1) begin
  assign outFF[i*WIDTH +: WIDTH] = inFF[selectFF*WIDTH +: WIDTH];
end endgenerate

endmodule
