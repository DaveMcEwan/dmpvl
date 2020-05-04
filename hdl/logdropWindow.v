
/* WIP/UNTESTED Windowing function "logdrop".
t ∈ [0, n); w(t) = 2**(⌊log₂min(t, n-t-1)⌋ - log₂(n/4))
x(t) ∈ (0, 1]; y(t) = w(t) x(t);

"fx-format" is mostly equivalent to Q-format minus a 1 in the LSB, though the
semantics are slightly different so it's not a completely 1-to-1 mapping.
The main difference is that Q-format with 0 unit bits and k fraction bits
represents the range [0, 1), whereas fx-format represents (0, 1].
E.g.

  Decimal   Q-format Bits   Q-format Range    fx-format Bits    fx-format Range
  -------   -------------   --------------    --------------    ---------------
  1.0       1.000           [0.9375, 1)       .1111             (0.9375, 1]
  0.0       0.000           [0, 0.125)        .0000             (0, 0.125]
  0.125     0.001           [0, 0.125)        .0000             (0, 0.125]
  0.25      0.010           [0.1875, 0.25)    .0011             (0.1875, 0.25]
  0.5       0.100           [0.4375, 0.25)    .0111             (0.4375, 0.25]

Inputs may be in either Q-format or fx-format, meaning that '0 is the smallest
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
generate if (ABSTRACT_MODEL) begin
`ifndef SYNTHESIS
  // Translation from Python plotting script.

  int t, x, y, n, onehotIdxN, a, shft;

  always @* begin
    x = i_x;
    n = WINLEN;

    // NOTE: Use the "proper math" notation (1-indexed) instead of "comp-sci"
    // notation (0-indexed).
    t = i_t + 1;

    // n must be a power of 2 so only a single bit set.
    // The power is the index of the set bit.
    onehotIdxN = $clog2(n/2);

    // min(t, WINLEN-t-1) increments then decrements with t.
    // Use a sawtooth counter, or opposing up/down counters.
    if (t <= n / 2)
        a = t;
    else
        a = n - t + 1;

    shft = onehotIdxN - $clog2(a);

    y = x >> shft;
  end

  assign o_y = y;

`endif
end else begin

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
wire [SHIFT_W-1:0] shft = WINLEN_W_M1_[SHIFT_W-1:0] - flog2a;

// Multiply inputs by w(t).
assign o_y = centerHalf ? i_x : (i_x >> shft);

end endgenerate

endmodule
