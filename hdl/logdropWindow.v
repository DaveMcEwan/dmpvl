`include "dff.vh"
`include "asrt.vh"
`include "misc.vh"

/* WIP/UNTESTED windowing function logdrop.
t ∈ [0, n); w(t) = 2**(⌊log₂min(t, n-t-1)⌋ - log₂(n/4))
x(t) ∈ (0, 1]; y(t) = w(t) x(t);

"fx-format" is mostly equivalent to Q-format minus a 1 in the LSB, though the
semantics are slightly different so it's not a completely 1-to-1 mapping.
The main difference is that Q-format with 0 unit bits and k fraction bits
represents the range [0, 1), whereas fx-format represents (0, 1].
E.g.
  1.0 (decimal) = 1.000 (Q-format) ~= .1111 (fx-format)
  0.0 (decimal) = 0.000 (Q-format) ~= .0000 (fx-format)
  0.125 (decimal) 0.001 (Q-format) ~= .0000 (fx-format)
  0.25 (decimal) 0.010 (Q-format) ~= .0011 (fx-format)
  0.5 (decimal) 0.100 (Q-format) ~= .0111 (fx-format)

Real inputs must be in fx-format, meaning that '0 is the smallest
representable number, and '1 is the largest representable number.

Bit inputs are converted to reals by simply replicating the bit.
The output values are ordered with bit-inputs in the lower indexes, and
real-inputs in the higher indexes.
*/
module windowLogdrop #(
  parameter N_IN_BITS   = 5,
  parameter N_IN_REALS  = 5,
  parameter DATA_W      = 8,
  parameter WINLEN      = 32, // Must be power-of-2, at least 8.
  parameter N_IN_ = N_IN_BITS + N_IN_REALS
) (
  input  wire                           i_clk,
  input  wire                           i_cg,
  input  wire                           i_rst,

  // Input bits and qfmts are only sampled when this is high.
  // Should usually come from an external wrapping counter.
  input  wire                           i_sample,

  input  wire [N_IN_BITS-1:0]           i_xBits,
  input  wire [N_IN_REALS*DATA_W-1:0]   i_xReals,
  output wire [N_IN_*DATA_W-1:0]        o_y
);

genvar i;

// {{{ Promote all inputs to same type/size.

wire [DATA_W-1:0] xBits  [N_IN_BITS];
generate for (i=0; i < N_IN_BITS; i=i+1) begin : promoteBits_b
  assign xBits[i] = {DATA_W{i_xBits[i]}};
end : promoteBits_b endgenerate

// Combine all input types into one unpacked vector.
localparam BITS_L = 0;
localparam BITS_H = N_IN_BITS - 1;
localparam REALS_L = BITS_H + 1;
localparam REALS_H = REALS_L + N_IN_REALS - 1;
wire [DATA_W-1:0] x [N_IN_];
generate for (i=0; i < N_IN_; i=i+1) begin : combineInputs_b
  if (BITS_H >= i)
    assign x[i] = xBits[i - BITS_L];
  else
    assign x[i] = i_xReals[DATA_W*(i - REALS_L) +: DATA_W];
end : combineInputs_b endgenerate

// }}} Promote all inputs to same type/size.

// Wrapping window index tracker.
localparam WINLEN_W = $clog2(WINLEN); // 16 --> 4
`dff_cg_srst(reg [WINLEN_W-1:0], t, i_clk, i_cg, i_rst, '0)
always @*
  if (i_sample)
    t_d = t_q - 'd1;
  else
    t_d = t_q;


wire firstHalf = !t_q[WINLEN_W-1];
wire centerHalf = ^t_q[WINLEN_W-1:WINLEN_W-2];
wire lastHalf = t_q[WINLEN_W-1];

// a = min(t, n-t-1)
wire [WINLEN_W-1:0] a = lastHalf ? ~t_q : t_q;

// Take off top 2 bits of a, find flog2() of those bits.
wire [WINLEN_W-3:0] flog2a;
fxcs #(
  .WIDTH (WINLEN_W-2)
) onlyMsb_u (
  .i_target   ('1),
  .i_vector   (a[WINLEN_W-3:0]),
  .o_onehot   (flog2a)
);

/* Where n=16:
  - Smallest w(t) multiplier (largest shift), is 1/8 (>> 3).
  - Largest w(t) multiplier (smallest shift), is 1 (>> 0).
*/
localparam SHIFT_W = $clog2(WINLEN_W); // 4 --> 2
localparam WINLEN_W_M1_ = WINLEN_W-1;
wire [SHIFT_W-1:0] shft = centerHalf ? '0 : WINLEN_W_M1_[SHIFT_W-1:0] - flog2a;

// Multiply inputs by w(t).
wire [DATA_W-1:0] y [N_IN_];
generate for (i=0; i < N_IN_; i=i+1) begin : scale_b
  assign y[i] = x[i] >> shft;
  assign o_y[DATA_W*i +: DATA_W] = y[i];
end : scale_b endgenerate

endmodule
