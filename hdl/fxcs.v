/** fxcs_m.sv - Find XOR-Closest Set
 * Search an input vector for the bit set which is closest to i_target by the
 * XOR metric.
 * Output a onehot vector with only that bit set.
 * To use as a find-first-set, tie i_target to '0.
 * To use as a find-last-set, tie i_target to '1.
 * Purely combinatorial.
 */
module fxcs #(
  parameter WIDTH = 9, // Must be 2 or more.
  parameter ABSTRACT_MODEL = 0 // Set for faster simulation.
) (
  input  wire [$clog2(WIDTH)-1:0] i_target,
  input  wire [WIDTH-1:0]         i_vector,
  output wire [WIDTH-1:0]         o_onehot
);

localparam N_LEVELS = $clog2(WIDTH);
localparam WIDTH2 = 1 << N_LEVELS;

generate if (ABSTRACT_MODEL) begin : abstractModel
  integer i;
  integer index;

  reg [WIDTH-1:0] onehotResult;
  always @* begin
    onehotResult = '0;
    for (i = 0; i < WIDTH2; i=i+1) begin
                                                  /* verilator lint_off WIDTH */
      index = i ^ i_target;
                                                  /* verilator lint_on  WIDTH */
      if ((onehotResult == '0) && i_vector[index])
          onehotResult[index] = 1'b1;
    end
  end

  assign o_onehot = onehotResult;
end : abstractModel
else begin : realModel
  genvar level;
  genvar b;

  // Pad out input vector to next power of 2.
  reg [WIDTH2-1:0] paddedVector;
  always @* begin
    paddedVector = '0;
    paddedVector[WIDTH-1:0] = i_vector;
  end

  wire [WIDTH2-1:0] selnand [N_LEVELS];
  for (level=0; level < N_LEVELS; level=level+1) begin : selNandLevel
    localparam SEL_W = 1 << level;
    wire tgtBit = i_target[level];

    for (b=0; b < WIDTH2; b=b+1) begin : selNandBit
      localparam B = b >> level;
      localparam SEL_L = (B ^ 1) << level;

      wire anySel = |paddedVector[SEL_L +: SEL_W];

      assign selnand[level][b] = anySel && (B[0] ? !tgtBit : tgtBit);
    end : selNandBit
  end : selNandLevel

                                          // UNOPTFLAT allowed because this is
                                          // not really circular logic.
                                          /* verilator lint_off UNOPTFLAT */
  wire [WIDTH2-1:0] seltree [N_LEVELS+1];
                                          /* verilator lint_on  UNOPTFLAT */

  assign seltree[0] = paddedVector;
  for (level=0; level < N_LEVELS; level=level+1) begin : selTreeLevel
    assign seltree[level+1] = seltree[level] & ~selnand[level];
  end : selTreeLevel

  assign o_onehot = seltree[N_LEVELS][WIDTH-1:0];

end : realModel endgenerate

endmodule

