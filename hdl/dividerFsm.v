`include "dff.vh"
`include "asrt.vh"
`include "misc.vh"

// WIP Divider based on FSM
// TODO: Get this working before unrolled pipeline.
// TODO: Handshake/valid interface is dodgy.

// www.ece.lsu.edu_ee3755_2012f_l07.v.html
// (Patterson & Henessey, Computer Organization & Design, 4th Ed, Figure 4.41)
module dividerFsm #(
  parameter WIDTH = 8
) (
  input  wire             i_clk,
  input  wire             i_cg,
  input  wire             i_rst,

  input  wire             i_valid,
  input  wire [WIDTH-1:0] i_dividend,
  input  wire [WIDTH-1:0] i_divisor,

  output wire             o_valid,
  output wire [WIDTH-1:0] o_quotient,
  output wire [WIDTH-1:0] o_remainder
);

localparam IDX_W = $clog2(WIDTH) + 1;

`dff_cg_norst(reg [IDX_W-1:0], idx, i_clk, i_cg && (idx_q != '0))
always @*
  if (i_valid)
    idx_d = WIDTH;
  else
    idx_d = idx_q - 'd1;

// TODO: Definitely wrong!
assign o_valid = (idx_q == '0);

`dff_cg_norst(reg [2*WIDTH-1:0], qr, i_clk, i_cg)
wire [WIDTH:0] diff = qr_q[2*WIDTH-1:WIDTH-1] - {1'b0, i_divisor};
always @*
  if (i_valid)
    qr_d = {{WIDTH{1'b0}}, i_divisor};
  else if (diff[WIDTH])
    qr_d = qr_q << 1;
  else
    qr_d = {diff[WIDTH-1:0], qr_q[WIDTH-2:0], 1'b1};

assign o_remainder = qr_q[2*WIDTH-1:WIDTH];
assign o_quotient = qr_q[WIDTH-1:0];

endmodule
