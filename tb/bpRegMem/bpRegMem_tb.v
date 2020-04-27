/** bpRegMem_tb.v - Testbench for bpRegMem
 * Instance multiple bpRegMems with different parameters.
 * Instance name should be u_bpRegMem_<N_REG>
 * Connecting wires should be <instance>_<port>
 */
module bpRegMem_tb (

  // {{{ Default parameters.
  output wire [ 7:0]    bpRegMem_63_o_bp_data,
  output wire           bpRegMem_63_o_bp_valid,
  output wire           bpRegMem_63_o_bp_ready,
  // }}} Default parameters.

  // {{{ Minimal parameters.
  output wire [ 7:0]    bpRegMem_2_o_bp_data,
  output wire           bpRegMem_2_o_bp_valid,
  output wire           bpRegMem_2_o_bp_ready,
  // }}} Minimal parameters.

  // {{{ Maximal parameters.
  output wire [ 7:0]    bpRegMem_127_o_bp_data,
  output wire           bpRegMem_127_o_bp_valid,
  output wire           bpRegMem_127_o_bp_ready,
  // }}} Maximal parameters.

  // {{{ Non-pow2.
  output wire [ 7:0]    bpRegMem_5_o_bp_data,
  output wire           bpRegMem_5_o_bp_valid,
  output wire           bpRegMem_5_o_bp_ready,
  // }}} Non-pow2.

  output reg            common_cg,
  output wire [ 7:0]    common_bp_data,
  output reg            common_bp_valid,
  output reg            common_bp_ready,

  input  wire           i_clk,
  input  wire           i_rst
);

reg [31:0] common_bp_data_32b;

always @(posedge i_clk) begin
  common_cg       <= ($random % 100) != 0; // Drop i_cg 1/100.
  common_bp_valid <= ($random % 5) == 0; // Pulse i_bp_valid 1/5.
  common_bp_ready <= ($random % 6) != 0; // Drop i_bp_ready 1/6.
  common_bp_data_32b <= $random;
end
assign common_bp_data = common_bp_data_32b[7:0];

// {{{ Default parameters.
bpRegMem #(
  .VALUE0  (8'h00),
  .N_REG  (63)
) u_bpRegMem_63 (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_bp_data  (common_bp_data),
  .i_bp_valid (common_bp_valid),
  .o_bp_ready (bpRegMem_63_o_bp_ready),

  .o_bp_data  (bpRegMem_63_o_bp_data),
  .o_bp_valid (bpRegMem_63_o_bp_valid),
  .i_bp_ready (common_bp_ready)
);
// }}} Default parameters.

// {{{ Minimal parameters.
bpRegMem #(
  .VALUE0  (8'h55),
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
  .VALUE0  (8'h56),
  .N_REG  (127)
) u_bpRegMem_127 (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_bp_data  (common_bp_data),
  .i_bp_valid (common_bp_valid),
  .o_bp_ready (bpRegMem_127_o_bp_ready),

  .o_bp_data  (bpRegMem_127_o_bp_data),
  .o_bp_valid (bpRegMem_127_o_bp_valid),
  .i_bp_ready (common_bp_ready)
);
// }}} Maximal parameters.

// {{{ Non-pow2.
bpRegMem #(
  .VALUE0  (8'h57),
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
