/** bpRegMem_tb.v - Testbench for bpRegMem
 * Instance multiple bpRegMems with different parameters.
 * Instance name should be u_bpRegMem_<N_REG>
 * Connecting wires should be <instance>_<port>
 */
module bpRegMem_tb (

  // {{{ Default parameters.
  input  wire           bpRegMem_64_i_clk,
  input  wire           bpRegMem_64_i_rst,
  input  wire           bpRegMem_64_i_cg,
  input  wire [ 7:0]    bpRegMem_64_i_bp_data,
  input  wire           bpRegMem_64_i_bp_valid,
  output wire           bpRegMem_64_o_bp_ready,
  output wire [ 7:0]    bpRegMem_64_o_bp_data,
  output wire           bpRegMem_64_o_bp_valid,
  input  wire           bpRegMem_64_i_bp_ready,
  // }}} Default parameters.

  // {{{ Minimal parameters.
  input  wire           bpRegMem_2_i_clk,
  input  wire           bpRegMem_2_i_rst,
  input  wire           bpRegMem_2_i_cg,
  input  wire [ 7:0]    bpRegMem_2_i_bp_data,
  input  wire           bpRegMem_2_i_bp_valid,
  output wire           bpRegMem_2_o_bp_ready,
  output wire [ 7:0]    bpRegMem_2_o_bp_data,
  output wire           bpRegMem_2_o_bp_valid,
  input  wire           bpRegMem_2_i_bp_ready,
  // }}} Minimal parameters.

  // {{{ Maximal parameters.
  input  wire           bpRegMem_128_i_clk,
  input  wire           bpRegMem_128_i_rst,
  input  wire           bpRegMem_128_i_cg,
  input  wire [ 7:0]    bpRegMem_128_i_bp_data,
  input  wire           bpRegMem_128_i_bp_valid,
  output wire           bpRegMem_128_o_bp_ready,
  output wire [ 7:0]    bpRegMem_128_o_bp_data,
  output wire           bpRegMem_128_o_bp_valid,
  input  wire           bpRegMem_128_i_bp_ready,
  // }}} Maximal parameters.

  // {{{ Non-pow2.
  input  wire           bpRegMem_5_i_clk,
  input  wire           bpRegMem_5_i_rst,
  input  wire           bpRegMem_5_i_cg,
  input  wire [ 7:0]    bpRegMem_5_i_bp_data,
  input  wire           bpRegMem_5_i_bp_valid,
  output wire           bpRegMem_5_o_bp_ready,
  output wire [ 7:0]    bpRegMem_5_o_bp_data,
  output wire           bpRegMem_5_o_bp_valid,
  input  wire           bpRegMem_5_i_bp_ready,
  // }}} Non-pow2.

  input  wire           i_clk,
  input  wire           i_rst,
  input  wire           common_cg,
  input  wire [ 7:0]    common_bp_data,
  input  wire           common_bp_valid,
  input  wire           common_bp_ready
);

// {{{ Default parameters.
bpRegMem #(
  .N_REG  (64)
) u_bpRegMem_64 (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_bp_data  (common_bp_data),
  .i_bp_valid (common_bp_valid),
  .o_bp_ready (bpRegMem_64_o_bp_ready),

  .o_bp_data  (bpRegMem_64_o_bp_data),
  .o_bp_valid (bpRegMem_64_o_bp_valid),
  .i_bp_ready (common_bp_ready)
);
// }}} Default parameters.

// {{{ Minimal parameters.
bpRegMem #(
  .N_REG  (2)
) u_bpRegMem_2 (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_bp_data  (common_bp_data),
  .i_bp_valid (common_bp_valid),
  .o_bp_ready (bpRegMem_2_o_bp_ready),

  .o_bp_data  (bpRegMem_2_o_bp_data),
  .o_bp_valid (bpRegMem_2_o_bp_valid),
  .i_bp_ready (common_bp_ready)
);
// }}} Minimal parameters.

// {{{ Maximal parameters.
bpRegMem #(
  .N_REG  (128)
) u_bpRegMem_128 (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_bp_data  (common_bp_data),
  .i_bp_valid (common_bp_valid),
  .o_bp_ready (bpRegMem_128_o_bp_ready),

  .o_bp_data  (bpRegMem_128_o_bp_data),
  .o_bp_valid (bpRegMem_128_o_bp_valid),
  .i_bp_ready (common_bp_ready)
);
// }}} Maximal parameters.

// {{{ Non-pow2.
bpRegMem #(
  .N_REG  (5)
) u_bpRegMem_5 (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_bp_data  (common_bp_data),
  .i_bp_valid (common_bp_valid),
  .o_bp_ready (bpRegMem_5_o_bp_ready),

  .o_bp_data  (bpRegMem_5_o_bp_data),
  .o_bp_valid (bpRegMem_5_o_bp_valid),
  .i_bp_ready (common_bp_ready)
);
// }}} Non-pow2.

endmodule
