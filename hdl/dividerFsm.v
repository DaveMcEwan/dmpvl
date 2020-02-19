`include "dff.vh"
`include "asrt.vh"
`include "misc.vh"

// WIP Divider based on FSM
// TODO: Get this working before unrolled pipeline.

// www.ece.lsu.edu_ee3755_2012f_l07.v.html
// (Patterson & Henessey, Computer Organization & Design, 4th Ed, Figure 4.41)
module dividerFsm #(
  parameter WIDTH = 8,
  parameter ABSTRACT_MODEL = 0 // Set for faster simulation.
) (
  input  wire             i_clk,
  input  wire             i_cg,
  input  wire             i_rst,

  // Single pulse to begin the calculation.
  input  wire             i_begin,
  input  wire [WIDTH-1:0] i_dividend,
  input  wire [WIDTH-1:0] i_divisor,

  // Outputs may be sampled when o_busy is clear.
  output wire             o_busy,
  output wire [WIDTH-1:0] o_quotient,
  output wire [WIDTH-1:0] o_remainder
);

`dff_cg_srst(reg [$clog2(WIDTH):0], fsm, i_clk, i_cg, i_rst, '0)
always @*
  if (i_begin)
    fsm_d = WIDTH;
  else if (fsm_q != '0)
    fsm_d = fsm_q - 'd1;
  else
    fsm_d = fsm_q;

assign o_busy = (fsm_q != '0);

`dff_cg_norst_d(reg [WIDTH-1:0], divisor, i_clk, i_cg, i_divisor)

generate if (ABSTRACT_MODEL) begin : abstractModel
  // NOTE: When i_dividend==0, results are NaN.
  wire divByZero = (i_divisor == '0);
  assign o_remainder = divByZero ? i_dividend : i_dividend % i_divisor;
  assign o_quotient  = divByZero ? '1         : i_dividend / i_divisor;
end : abstractModel
else begin : realModel

  `dff_cg_norst(reg [2*WIDTH-1:0], qr, i_clk, i_cg)

  wire [WIDTH:0] diff = qr_q[2*WIDTH-1:WIDTH-1] - {1'b0, divisor_q};

  always @*
    if (i_begin)
      qr_d = {{WIDTH{1'b0}}, i_dividend};
    else if (diff[WIDTH])
      qr_d = qr_q << 1;
    else
      qr_d = {diff[WIDTH-1:0], qr_q[WIDTH-2:0], 1'b1};

  assign o_remainder = qr_q[2*WIDTH-1:WIDTH];
  assign o_quotient = qr_q[WIDTH-1:0];

end : realModel endgenerate

endmodule
