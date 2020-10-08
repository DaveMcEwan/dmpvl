/** correlator_tb.v - Testbench for correlator with BytePipe interface.
 * Expose BytePipe as a PTY for external script to use.
 */
`include "dff.svh"

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

localparam MAX_WINDOW_LENGTH_EXP  = 16;
localparam MAX_SAMPLE_PERIOD_EXP  = 15;
localparam MAX_SAMPLE_JITTER_EXP  = 8;
localparam WINDOW_PRECISION       = 8;
localparam METRIC_PRECISION       = 16;
localparam PKTFIFO_DEPTH          = 50;

// bpReg registers to correlator
localparam WINDOW_LENGTH_EXP_W      = $clog2(MAX_WINDOW_LENGTH_EXP+1);
localparam SAMPLE_PERIOD_EXP_W      = $clog2(MAX_SAMPLE_PERIOD_EXP+1);
localparam SAMPLE_JITTER_EXP_W      = $clog2(MAX_SAMPLE_JITTER_EXP+1);
localparam LED_SOURCE_W             = 3;

wire [WINDOW_LENGTH_EXP_W-1:0]    windowLengthExp;
wire                              windowShape;
wire [SAMPLE_PERIOD_EXP_W-1:0]    samplePeriodExp;
wire [SAMPLE_JITTER_EXP_W-1:0]    sampleJitterExp;
wire [LED_SOURCE_W-1:0]           ledSource;

wire [7:0]                        pktfifo_o_data;
wire                              pktfifo_o_empty;
wire                              pktfifo_i_pop;
wire                              pktfifo_i_flush;

wire [7:0]                        jitterSeedByte;
wire                              jitterSeedValid;

wire                              ledPwm;

bpReg #(
  .PKTFIFO_DEPTH            (PKTFIFO_DEPTH), // Bytes, not packets.
  .MAX_WINDOW_LENGTH_EXP    (MAX_WINDOW_LENGTH_EXP),
  .WINDOW_PRECISION         (WINDOW_PRECISION),
  .MAX_SAMPLE_PERIOD_EXP    (MAX_SAMPLE_PERIOD_EXP),
  .MAX_SAMPLE_JITTER_EXP    (MAX_SAMPLE_JITTER_EXP)
) u_bpReg (
  .i_clk                  (i_clk),
  .i_rst                  (i_rst),
  .i_cg                   (common_cg),

  .i_pktfifo_data         (pktfifo_o_data),
  .i_pktfifo_empty        (pktfifo_o_empty),
  .o_pktfifo_pop          (pktfifo_i_pop),
  .o_pktfifo_flush        (pktfifo_i_flush),

  .o_reg_windowLengthExp  (windowLengthExp),
  .o_reg_windowShape      (windowShape),
  .o_reg_samplePeriodExp  (samplePeriodExp),
  .o_reg_sampleJitterExp  (sampleJitterExp),
  .o_reg_ledSource        (ledSource),

  .o_jitterSeedByte       (jitterSeedByte),
  .o_jitterSeedValid      (jitterSeedValid),

  .i_bp_data              (bp0_upstream_data),
  .i_bp_valid             (bp0_upstream_valid),
  .o_bp_ready             (bp0_upstream_ready),

  .o_bp_data              (bp0_dnstream_data),
  .o_bp_valid             (bp0_dnstream_valid),
  .i_bp_ready             (bp0_dnstream_ready)
);

correlator #(
  .MAX_WINDOW_LENGTH_EXP    (MAX_WINDOW_LENGTH_EXP),
  .MAX_SAMPLE_PERIOD_EXP    (MAX_SAMPLE_PERIOD_EXP),
  .MAX_SAMPLE_JITTER_EXP    (MAX_SAMPLE_JITTER_EXP),
  .WINDOW_PRECISION         (WINDOW_PRECISION),
  .METRIC_PRECISION         (METRIC_PRECISION),
  .PKTFIFO_DEPTH            (PKTFIFO_DEPTH) // Bytes, not packets.
) u_correlator (
  .i_clk                  (i_clk),
  .i_rst                  (i_rst),
  .i_cg                   (common_cg),

  .o_pktfifo_data         (pktfifo_o_data),
  .o_pktfifo_empty        (pktfifo_o_empty),
  .i_pktfifo_pop          (pktfifo_i_pop),
  .i_pktfifo_flush        (pktfifo_i_flush),

  .i_windowLengthExp      (windowLengthExp),
  .i_windowShape          (windowShape),
  .i_samplePeriodExp      (samplePeriodExp),
  .i_sampleJitterExp      (sampleJitterExp),
  .i_ledSource            (ledSource),

  .i_jitterSeedByte       (jitterSeedByte),
  .i_jitterSeedValid      (jitterSeedValid),

  .i_x                    (common_x),
  .i_y                    (common_y),

  .o_ledPwm               (ledPwm)
);

endmodule
