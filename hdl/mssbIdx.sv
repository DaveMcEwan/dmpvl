/** mssbIdx.v - Calculate the index of the most significant set bit.
 * mssb(x) := max(y | 2**y ≤ x)
 * o_index = max(o_index | 2**o_index ≤ i_vector)
 * Purely combinatorial.
 */
module mssbIdx #(
  parameter WIDTH = 7, // Must be 1 or more.
  parameter ABSTRACT_MODEL = 0 // Set for faster simulation.
) (
  input  wire [WIDTH-1:0]            i_vector,
  output wire [$clog2(WIDTH)-1:0]    o_index,
  output wire                        o_valid
);

generate if (ABSTRACT_MODEL) begin : abstractModel
  integer i;
  reg [$clog2(WIDTH)-1:0] indexResult;

  always @* begin
    indexResult = '0;
    for (i = 0; i < WIDTH; i=i+1) begin
      if ((i_vector & (1 << i)) != '0)
          indexResult = i[$clog2(WIDTH)-1:0];
    end
  end

  assign o_index = indexResult;
end : abstractModel
else begin : realModel

  wire [WIDTH-1:0] vec_onehot;

  fxcs #(
    .WIDTH (WIDTH)
  ) mssb_u (
    .i_target   ({$clog2(WIDTH){1'b1}}),
    .i_vector   (i_vector),
    .o_onehot   (vec_onehot)
  );

  wire _unused_anySet;
  onehotIdx #(
    .WIDTH (WIDTH)
  ) idx_u (
    .i_onehot   (vec_onehot),
    .o_index    (o_index),
    .o_valid    (_unused_anySet)
  );

end : realModel endgenerate

assign o_valid = |i_vector;

endmodule
