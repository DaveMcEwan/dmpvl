/** WIP
w_rand.sv - Simulate applying logdropWindow to a uniform random variable.
 * Purely combinatorial.
 */
module w_rand (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire [31:0]  i_t,
  input  wire [31:0]  i_x,

  output wire [7:0]   A_i_t,
  output wire [7:0]   A_i_x,
  output wire [ 7:0]  A_o_y,
  output wire [ 7:0]  A_abstract_o_y
`endif
);

assign A_i_t = i_t[7:0];
assign A_i_x = i_x[7:0];

logdropWindow #(
  .DATA_W         (8),
  .WINLEN         (256),
  .ABSTRACT_MODEL (0)
) A_u (
  .i_t  (A_i_t),
  .i_x  (A_i_x),
  .o_y  (A_o_y)
);

logdropWindow #(
  .DATA_W         (8),
  .WINLEN         (256),
  .ABSTRACT_MODEL (1)
) A_abstract_u (
  .i_t  (A_i_t),
  .i_x  (A_i_x),
  .o_y  (A_abstract_o_y)
);

endmodule
