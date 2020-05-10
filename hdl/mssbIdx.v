/** mssbIdx.v - Calculate the index of the most significant set bit.
 * Purely combinatorial.
 */
module mssbIdx #(
  parameter WIDTH = 7 // Must be 1 or more.
) (
  input  wire [WIDTH-1:0]            i_vector,
  output wire [$clog2(WIDTH)-1:0]    o_index,
  output wire                        o_valid
);

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

assign o_valid = |i_vector;

endmodule
