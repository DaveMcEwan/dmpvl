/** correlator_tb.v - Testbench for fifo
 * Expose BytePipe as a PTY for external script to use.
 */
`include "dff.vh"

module correlator_tb (

  output reg            common_x,
  output reg            common_y,

  output reg            common_cg,

  input  wire           i_clk,
  input  wire           i_rst

);

always @(posedge i_clk) begin
  common_cg     <= ($random % 100) != 0; // Drop i_cg 1/100.
  common_x      <= ($random % 5) == 0; // Pulse X high 1/5.
  common_y      <= ($random % 6) == 0; // Pulse Y high 1/6.
end
`dff_upcounter(reg [31:0], nCycles, i_clk, 1'b1, i_rst)

wire [7:0]  bp0_upstream_data;
wire        bp0_upstream_valid;
wire        bp0_upstream_ready;
wire [7:0]  bp0_dnstream_data;
wire        bp0_dnstream_valid;
wire        bp0_dnstream_ready;
ptyBytePipe #(
  .NUMBER  (0)
) u_bp0 ( // {{{
  .i_clk        (i_clk),
  .i_rst        (i_rst),
  .i_cg         (common_cg),

  .i_verboseOn  (1'b0),
  .i_verboseOff (1'b0),

  .o_bpUpstream_data  (bp0_upstream_data),
  .o_bpUpstream_valid (bp0_upstream_valid),
  .i_bpUpstream_ready (bp0_upstream_ready),

  .i_bpDnstream_data  (bp0_dnstream_data),
  .i_bpDnstream_valid (bp0_dnstream_valid),
  .o_bpDnstream_ready (bp0_dnstream_ready)
); // }}}

correlator u_correlator (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_x        (common_x),
  .i_y        (common_y),

  .i_bp_data  (bp0_upstream_data),
  .i_bp_valid (bp0_upstream_valid),
  .o_bp_ready (bp0_upstream_ready),

  .o_bp_data  (bp0_dnstream_data),
  .o_bp_valid (bp0_dnstream_valid),
  .i_bp_ready (bp0_dnstream_ready)
);

endmodule
