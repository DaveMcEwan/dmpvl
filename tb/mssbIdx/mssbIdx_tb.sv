/** mssbIdx_tb.sv - Testbench for mssbIdx
 * Exhaustively test all valid input combinations.
 * Instance name should be u_mssbIdx_<WIDTH>
 * Connecting wires should be <instance>_<port>
 * Purely combinatorial.
 */
module mssbIdx_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire [15:0]  mssbIdx_16_i_vector,
  output wire [ 3:0]  mssbIdx_16_o_index,
  output wire [ 3:0]  mssbIdx_16_abstract_o_index,
  output wire         mssbIdx_16_o_valid,

  input  wire [ 8:0]  mssbIdx_9_i_vector,
  output wire [ 3:0]  mssbIdx_9_o_index,
  output wire [ 3:0]  mssbIdx_9_abstract_o_index,
  output wire         mssbIdx_9_o_valid,

  input  wire [ 6:0]  mssbIdx_7_i_vector,
  output wire [ 2:0]  mssbIdx_7_o_index,
  output wire [ 2:0]  mssbIdx_7_abstract_o_index,
  output wire         mssbIdx_7_o_valid
`endif
);

mssbIdx #(
  .WIDTH  (16),
  .ABSTRACT_MODEL (0)
) u_mssbIdx_16 (
  .i_vector   (mssbIdx_16_i_vector),
  .o_index    (mssbIdx_16_o_index),
  .o_valid    (mssbIdx_16_o_valid)
);

mssbIdx #(
  .WIDTH  (16),
  .ABSTRACT_MODEL (1)
) u_mssbIdx_16_abstract (
  .i_vector   (mssbIdx_16_i_vector),
  .o_index    (mssbIdx_16_abstract_o_index),
  .o_valid    ()
);

mssbIdx #(
  .WIDTH  (9),
  .ABSTRACT_MODEL (0)
) u_mssbIdx_9 (
  .i_vector   (mssbIdx_9_i_vector),
  .o_index    (mssbIdx_9_o_index),
  .o_valid    (mssbIdx_9_o_valid)
);

mssbIdx #(
  .WIDTH  (9),
  .ABSTRACT_MODEL (1)
) u_mssbIdx_9_abstract (
  .i_vector   (mssbIdx_9_i_vector),
  .o_index    (mssbIdx_9_abstract_o_index),
  .o_valid    ()
);

mssbIdx #(
  .WIDTH  (7),
  .ABSTRACT_MODEL (0)
) u_mssbIdx_7 (
  .i_vector   (mssbIdx_7_i_vector),
  .o_index    (mssbIdx_7_o_index),
  .o_valid    (mssbIdx_7_o_valid)
);

mssbIdx #(
  .WIDTH  (7),
  .ABSTRACT_MODEL (1)
) u_mssbIdx_7_abstract (
  .i_vector   (mssbIdx_7_i_vector),
  .o_index    (mssbIdx_7_abstract_o_index),
  .o_valid    ()
);

endmodule
