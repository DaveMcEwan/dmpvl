
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

Inputs must be in fx-format, meaning that '0 is the smallest
representable number, and '1 is the largest representable number.
*/
module logdropWindow #(
  parameter DATA_W = 8,
  parameter WINLEN = 32, // Must be power-of-2, at least 8.
  parameter ABSTRACT_MODEL = 0 // TODO
) (
  // Wrapping window index tracker.
  input  wire [$clog2(WINLEN)-1:0]      i_t,

  input  wire [DATA_W-1:0]              i_x,

  output wire [DATA_W-1:0]              o_y
);

localparam WINLEN_W = $clog2(WINLEN); // 16 --> 4

wire firstHalf = !i_t[WINLEN_W-1];
wire centerHalf = ^i_t[WINLEN_W-1:WINLEN_W-2];
wire lastHalf = i_t[WINLEN_W-1];

// a = min(t, n-t-1)
wire [WINLEN_W-1:0] a = lastHalf ? ~i_t : i_t;

// Take off top 2 bits of a, find flog2() of those bits.
wire [WINLEN_W-3:0] flog2a;
fxcs #(
  .WIDTH (WINLEN_W-2)
) onlyMsb_u (
  .i_target   ('1),
  .i_vector   (a[WINLEN_W-3:0]),
  .o_onehot   (flog2a)
);

// Where n=16:
//  - Smallest w(t) multiplier (largest shift), is 1/8 (>> 3).
//  - Largest w(t) multiplier (smallest shift), is 1 (>> 0).
localparam SHIFT_W = $clog2(WINLEN_W); // 4 --> 2
localparam WINLEN_W_M1_ = WINLEN_W-1;
wire [SHIFT_W-1:0] shft = centerHalf ? '0 : WINLEN_W_M1_[SHIFT_W-1:0] - flog2a;

// Multiply inputs by w(t).
assign o_y = i_x >> shft;

endmodule
