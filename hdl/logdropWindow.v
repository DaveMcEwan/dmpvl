/* Windowing function "logdrop"

Informally:
  Window-length (n) must be a power of 2 number of samples.
  Time is zero-indexed, and window coefficient is derived solely from time.
  Both input (x) and output (y) are in the range 0 to 1.
  Output is formed by multiplying input with window coefficient.

Formally:
  n = 2**p; p ∊ ℤ; p > 2
  t ∊ [0, n); w(t) = 2**( ⌈log₂min(t+1, n-t)⌉ - log₂(n/2) )
  x(t) ∊ (0, 1]; y(t) = w(t) x(t) ⇒ y(t) ∊ (0, 1]

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
  parameter WINLEN = 64, // Must be power-of-2, at least 8.
  parameter ABSTRACT_MODEL = 0
) (
  // Wrapping window index tracker.
  input  wire [$clog2(WINLEN)-1:0]      i_t,

  input  wire [DATA_W-1:0]              i_x,

  output wire [DATA_W-1:0]              o_y
);
generate if (ABSTRACT_MODEL) begin
`ifndef SYNTHESIS
/* Translation from Python plotting script.

NOTE: Uses the "proper math" notation (1-indexed) instead of "comp-sci"
notation (0-indexed).

# 1-indexed version
ts = np.arange(1, n+1, 1)
ws = [2**( ceil(log(min(t, n-t+1), 2)) - log(n/2, 2) ) for t in ts]

# Alternate 1-indexed version
def w_1idx(t, n):
    onehotIdxN = log2(n/2)

    # min(t, n-t-1) increments then decrements with t.
    # Use a bi-directional counter, or opposing up/down counters.
    if t <= n / 2:
        a = t
    else:
        a = n - t + 1

    shft = onehotIdxN - ceil(log(a, 2))

    return 1/2**shft
*/

  int t, x, y, n, onehotIdxN, a, shft;

  always @* begin
    x = 32'(i_x);
    n = WINLEN;

    t = 32'(i_t) + 1;

    // n must be a power of 2 --> log₂() equivalent to $clog2().
    onehotIdxN = $clog2(n/2);

    // min(t, WINLEN-t-1) increments then decrements with t.
    if (t <= n / 2)
        a = t;
    else
        a = n - t + 1;

    shft = onehotIdxN - $clog2(a);

    y = x >> shft;
  end

  assign o_y = y[DATA_W-1:0];

`endif
end else begin

// WINLEN=16 => WINLEN_W = 4
// WINLEN=32 => WINLEN_W = 5
// WINLEN=64 => WINLEN_W = 6
localparam WINLEN_W = $clog2(WINLEN);

wire firstHalf = !i_t[WINLEN_W-1];
wire centerHalf = ^i_t[WINLEN_W-1:WINLEN_W-2];
wire lastHalf = i_t[WINLEN_W-1];

// bi-directional counter derived from t counts from 0 thru 2**WINLEN-1, then down.
// a = min(t, n-t-1)
// WINLEN=16 => a in 0..7
// WINLEN=32 => a in 0..15
// WINLEN=64 => a in 0..31
localparam BICNTR_W = WINLEN_W - 1;
wire [BICNTR_W-1:0] a = lastHalf ? ~i_t[BICNTR_W-1:0] : i_t[BICNTR_W-1:0];

// Find index of most significant set bit of bi-directional counter.
// WINLEN=16 => aOnehotVld,Idx in (False,0),(True,0),(True,1),(True,2)
// WINLEN=32 => aOnehotVld,Idx in (False,0),(True,0),(True,1),(True,2),(True,3)
// WINLEN=64 => aOnehotVld,Idx in (False,0),(True,0),(True,1),(True,2),(True,3),(True,4)
localparam MUXIDX_W = $clog2(WINLEN_W);
wire [MUXIDX_W-1:0] aOnehotIdx;
wire aOnehotVld;
mssbIdx #(
  .WIDTH  (BICNTR_W)
) u_mssbIdx_7 (
  .i_vector   (a),
  .o_index    (aOnehotIdx),
  .o_valid    (aOnehotVld)
);

// WINLEN=16 => muxIdx in 0..3
// WINLEN=32 => muxIdx in 0..4
// WINLEN=64 => muxIdx in 0..5
wire [MUXIDX_W-1:0] muxIdx = aOnehotIdx + (aOnehotVld ? 1 : 0);

(* mem2reg *) reg [DATA_W-1:0] muxSrc [WINLEN_W];
genvar i;
for (i = 0; i < WINLEN_W; i=i+1) begin : muxSrc_b
  localparam SHIFT = BICNTR_W - i;
  always @* muxSrc[i] = i_x >> SHIFT;
end : muxSrc_b

assign o_y = muxSrc[muxIdx];

end endgenerate

endmodule
