/** fifo_tb.v - Testbench for fifo
 * Instance multiple fifos with different parameters.
 * Instance name should be u_fifo_<WIDTH>_<DEPTH>_(mem|flops)
 * Connecting wires should be <instance>_<port>
 */
module fifo_tb (

  // {{{ Default parameters.
  input  wire           fifo_8_8_mem_i_clk,
  input  wire           fifo_8_8_mem_i_rst,
  input  wire           fifo_8_8_mem_i_cg,
  input  wire           fifo_8_8_mem_i_flush,
  input  wire           fifo_8_8_mem_i_push,
  input  wire           fifo_8_8_mem_i_pop,
  input  wire [ 7:0]    fifo_8_8_mem_i_data,
  output wire [ 7:0]    fifo_8_8_mem_o_data,
  output wire           fifo_8_8_mem_o_empty,
  output wire           fifo_8_8_mem_o_full,
  output wire           fifo_8_8_mem_o_pushed,
  output wire           fifo_8_8_mem_o_popped,
  output wire [ 2:0]    fifo_8_8_mem_o_wrptr,
  output wire [ 2:0]    fifo_8_8_mem_o_rdptr,
  output wire [ 7:0]    fifo_8_8_mem_o_valid,
  output wire [ 3:0]    fifo_8_8_mem_o_nEntries,
  output wire [63:0]    fifo_8_8_mem_o_entries,
  // }}} Default parameters.

  // {{{ Minimal width and depth.
  input  wire           fifo_1_2_mem_i_clk,
  input  wire           fifo_1_2_mem_i_rst,
  input  wire           fifo_1_2_mem_i_cg,
  input  wire           fifo_1_2_mem_i_flush,
  input  wire           fifo_1_2_mem_i_push,
  input  wire           fifo_1_2_mem_i_pop,
  input  wire [ 0:0]    fifo_1_2_mem_i_data,
  output wire [ 0:0]    fifo_1_2_mem_o_data,
  output wire           fifo_1_2_mem_o_empty,
  output wire           fifo_1_2_mem_o_full,
  output wire           fifo_1_2_mem_o_pushed,
  output wire           fifo_1_2_mem_o_popped,
  output wire [ 0:0]    fifo_1_2_mem_o_wrptr,
  output wire [ 0:0]    fifo_1_2_mem_o_rdptr,
  output wire [ 1:0]    fifo_1_2_mem_o_valid,
  output wire [ 1:0]    fifo_1_2_mem_o_nEntries,
  output wire [ 1:0]    fifo_1_2_mem_o_entries,
  // }}} Minimal width and depth.

  // {{{ Non-pow2 width and depth.
  input  wire           fifo_5_5_mem_i_clk,
  input  wire           fifo_5_5_mem_i_rst,
  input  wire           fifo_5_5_mem_i_cg,
  input  wire           fifo_5_5_mem_i_flush,
  input  wire           fifo_5_5_mem_i_push,
  input  wire           fifo_5_5_mem_i_pop,
  input  wire [ 4:0]    fifo_5_5_mem_i_data,
  output wire [ 4:0]    fifo_5_5_mem_o_data,
  output wire           fifo_5_5_mem_o_empty,
  output wire           fifo_5_5_mem_o_full,
  output wire           fifo_5_5_mem_o_pushed,
  output wire           fifo_5_5_mem_o_popped,
  output wire [ 2:0]    fifo_5_5_mem_o_wrptr,
  output wire [ 2:0]    fifo_5_5_mem_o_rdptr,
  output wire [ 4:0]    fifo_5_5_mem_o_valid,
  output wire [ 2:0]    fifo_5_5_mem_o_nEntries,
  output wire [24:0]    fifo_5_5_mem_o_entries,
  // }}} Non-pow2 width and depth.

  // {{{ Flops, not memory block.
  input  wire           fifo_8_2_flops_i_clk,
  input  wire           fifo_8_2_flops_i_rst,
  input  wire           fifo_8_2_flops_i_cg,
  input  wire           fifo_8_2_flops_i_flush,
  input  wire           fifo_8_2_flops_i_push,
  input  wire           fifo_8_2_flops_i_pop,
  input  wire [ 7:0]    fifo_8_2_flops_i_data,
  output wire [ 7:0]    fifo_8_2_flops_o_data,
  output wire           fifo_8_2_flops_o_empty,
  output wire           fifo_8_2_flops_o_full,
  output wire           fifo_8_2_flops_o_pushed,
  output wire           fifo_8_2_flops_o_popped,
  output wire [ 0:0]    fifo_8_2_flops_o_wrptr,
  output wire [ 0:0]    fifo_8_2_flops_o_rdptr,
  output wire [ 1:0]    fifo_8_2_flops_o_valid,
  output wire [ 1:0]    fifo_8_2_flops_o_nEntries,
  output wire [15:0]    fifo_8_2_flops_o_entries,
  // }}} Flops, not memory block.

  input  wire           i_clk,
  input  wire           i_rst,
  input  wire           common_cg,
  input  wire           common_flush,
  input  wire           common_push,
  input  wire           common_pop,
  input  wire [31:0]    common_data

);

// {{{ Default parameters.
fifo #(
  .WIDTH          (8),
  .DEPTH          (8),
  .FLOPS_NOT_MEM  (0)
) u_fifo_8_8_mem (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_flush    (common_flush),
  .i_push     (common_push),
  .i_pop      (common_pop),

  .i_data     (fifo_8_8_mem_i_data),
  .o_data     (fifo_8_8_mem_o_data),

  .o_empty    (fifo_8_8_mem_o_empty),
  .o_full     (fifo_8_8_mem_o_full),

  .o_pushed   (fifo_8_8_mem_o_pushed),
  .o_popped   (fifo_8_8_mem_o_popped),

  .o_wrptr    (fifo_8_8_mem_o_wrptr),
  .o_rdptr    (fifo_8_8_mem_o_rdptr),

  .o_valid    (fifo_8_8_mem_o_valid),
  .o_nEntries (fifo_8_8_mem_o_nEntries),

  .o_entries  (fifo_8_8_mem_o_entries)
);
// }}} Default parameters.

// {{{ Minimal width and depth.
fifo #(
  .WIDTH          (1),
  .DEPTH          (2),
  .FLOPS_NOT_MEM  (0)
) u_fifo_1_2_mem (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_flush    (common_flush),
  .i_push     (common_push),
  .i_pop      (common_pop),

  .i_data     (fifo_1_2_mem_i_data),
  .o_data     (fifo_1_2_mem_o_data),

  .o_empty    (fifo_1_2_mem_o_empty),
  .o_full     (fifo_1_2_mem_o_full),

  .o_pushed   (fifo_1_2_mem_o_pushed),
  .o_popped   (fifo_1_2_mem_o_popped),

  .o_wrptr    (fifo_1_2_mem_o_wrptr),
  .o_rdptr    (fifo_1_2_mem_o_rdptr),

  .o_valid    (fifo_1_2_mem_o_valid),
  .o_nEntries (fifo_1_2_mem_o_nEntries),

  .o_entries  (fifo_1_2_mem_o_entries)
);
// }}} Minimal width and depth.

// {{{ Non-pow2 width and depth.
fifo #(
  .WIDTH          (5),
  .DEPTH          (5),
  .FLOPS_NOT_MEM  (0)
) u_fifo_5_5_mem (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_flush    (common_flush),
  .i_push     (common_push),
  .i_pop      (common_pop),

  .i_data     (fifo_5_5_mem_i_data),
  .o_data     (fifo_5_5_mem_o_data),

  .o_empty    (fifo_5_5_mem_o_empty),
  .o_full     (fifo_5_5_mem_o_full),

  .o_pushed   (fifo_5_5_mem_o_pushed),
  .o_popped   (fifo_5_5_mem_o_popped),

  .o_wrptr    (fifo_5_5_mem_o_wrptr),
  .o_rdptr    (fifo_5_5_mem_o_rdptr),

  .o_valid    (fifo_5_5_mem_o_valid),
  .o_nEntries (fifo_5_5_mem_o_nEntries),

  .o_entries  (fifo_5_5_mem_o_entries)
);
// }}} Non-pow2 width and depth.

// {{{ Flops, not memory block.
fifo #(
  .WIDTH          (8),
  .DEPTH          (2),
  .FLOPS_NOT_MEM  (1)
) u_fifo_8_2_flops (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_flush    (common_flush),
  .i_push     (common_push),
  .i_pop      (common_pop),

  .i_data     (fifo_8_2_flops_i_data),
  .o_data     (fifo_8_2_flops_o_data),

  .o_empty    (fifo_8_2_flops_o_empty),
  .o_full     (fifo_8_2_flops_o_full),

  .o_pushed   (fifo_8_2_flops_o_pushed),
  .o_popped   (fifo_8_2_flops_o_popped),

  .o_wrptr    (fifo_8_2_flops_o_wrptr),
  .o_rdptr    (fifo_8_2_flops_o_rdptr),

  .o_valid    (fifo_8_2_flops_o_valid),
  .o_nEntries (fifo_8_2_flops_o_nEntries),

  .o_entries  (fifo_8_2_flops_o_entries)
);
// }}} Flops, not memory block.

endmodule
