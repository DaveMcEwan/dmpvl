/** onehotIdx.v - Calculate the set index of a onehot vector.
 * Construct the index of a onehot vector by fanning out and ORing the
 * appropriate bits.
 * When no bit is set the default result is 0.
 * No attempt is made to do anything specific when multiple bits are set.
 * Purely combinatorial.
 */
module onehotIdx #(
  parameter WIDTH = 15 // Must be 1 or more.
) (
  input  wire [WIDTH-1:0]            i_onehot,
  output wire [$clog2(WIDTH)-1:0]    o_index,
  output wire                        o_valid
);
localparam LOGWIDTH = $clog2(WIDTH);
localparam WIDTH2 = 1 << LOGWIDTH;

// Round width up to next power of 2.
reg [WIDTH2-1:0] paddedOnehot;
always @* begin
  paddedOnehot = '0;
  paddedOnehot[WIDTH-1:0] = i_onehot;
end

wire [(WIDTH2/2)-1:0] idx_or [LOGWIDTH];
genvar g;
genvar i;
generate for (g = 0; g < LOGWIDTH; g=g+1) begin : gateGen
  for (i = 0; i < WIDTH2/2; i=i+1) begin : inputGen
    localparam START = (1 << g);
    localparam IDXBIT = START + (i & (START-1)) + ((i >> g) * 2 * START);

    assign idx_or[g][i] = paddedOnehot[IDXBIT];
  end : inputGen

  assign o_index[g] = |idx_or[g];
end : gateGen endgenerate

assign o_valid = |i_onehot;

endmodule
