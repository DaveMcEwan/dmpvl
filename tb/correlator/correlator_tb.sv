/** correlator_tb.v - Testbench for correlator with BytePipe interface.
 * Expose BytePipe as a PTY for external script to use.
 */
`include "dff.svh"

module correlator_tb (
  input  wire           i_clk,
  input  wire           i_rst,
  output reg            common_cg
);

localparam N_PROBE                = 4;
localparam N_PAIR                 = 2;
localparam MAX_WINDOW_LENGTH_EXP  = 16;
localparam MAX_SAMPLE_PERIOD_EXP  = 15;
localparam MAX_SAMPLE_JITTER_EXP  = 8;
localparam WINDOW_PRECISION       = 8;
localparam METRIC_PRECISION       = 16;
localparam PKTFIFO_DEPTH          = 50;

int i;
reg [N_PROBE-1:0] common_probe;
always @(posedge i_clk) begin
  common_cg <= ($random % 100) != 0; // Drop i_cg 1/100.

  // Pulse probes faster in lower bits.
  for (i = 0; i < N_PROBE; i=i+1) begin
    common_probe[i] = (($random % 5) == 0) && (($random % (i+1)) == 0);
  end
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

wire [N_PAIR-1:0] ledPwm;

bpCorrelator #(
  .N_PROBE                  (N_PROBE),
  .N_PAIR                   (N_PAIR),
  .PKTFIFO_DEPTH            (PKTFIFO_DEPTH), // Bytes, not packets.
  .MAX_WINDOW_LENGTH_EXP    (MAX_WINDOW_LENGTH_EXP),
  .WINDOW_PRECISION         (WINDOW_PRECISION),
  .MAX_SAMPLE_PERIOD_EXP    (MAX_SAMPLE_PERIOD_EXP),
  .MAX_SAMPLE_JITTER_EXP    (MAX_SAMPLE_JITTER_EXP)
) u_bpCorrelator (
  .i_clk                  (i_clk),
  .i_rst                  (i_rst),
  .i_cg                   (common_cg),

  .i_bp_data              (bp0_upstream_data),
  .i_bp_valid             (bp0_upstream_valid),
  .o_bp_ready             (bp0_upstream_ready),

  .o_bp_data              (bp0_dnstream_data),
  .o_bp_valid             (bp0_dnstream_valid),
  .i_bp_ready             (bp0_dnstream_ready),

  .i_probe                (common_probe),
  .o_ledPwm               (ledPwm)
);

endmodule
