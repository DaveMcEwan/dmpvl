
module bpCorrelator #(
  parameter N_PROBE               = 4, // 2..256
  parameter N_PAIR                = 2, // 1..8
  parameter MAX_WINDOW_LENGTH_EXP = 16,
  parameter MAX_SAMPLE_PERIOD_EXP = 15,
  parameter MAX_SAMPLE_JITTER_EXP = 8,
  parameter WINDOW_PRECISION      = 8, // 1 < p <= MAX_WINDOW_LENGTH_EXP
  parameter METRIC_PRECISION      = 16,
  parameter PKTFIFO_DEPTH         = 50
) (
  input  wire                       i_clk,
  input  wire                       i_rst,
  input  wire                       i_cg,

  // BytePipe incoming
  input  wire [7:0]                 i_bp_data,
  input  wire                       i_bp_valid,
  output wire                       o_bp_ready,
  // BytePipe outcoming
  output wire [7:0]                 o_bp_data,
  output wire                       o_bp_valid,
  input  wire                       i_bp_ready,


  input  wire [N_PROBE-1:0]         i_probe,

  output wire [N_PAIR-1:0]          o_ledPwm
);

genvar i;

// bpReg registers to correlator
localparam WINDOW_LENGTH_EXP_W      = $clog2(MAX_WINDOW_LENGTH_EXP+1);
localparam SAMPLE_PERIOD_EXP_W      = $clog2(MAX_SAMPLE_PERIOD_EXP+1);
localparam SAMPLE_JITTER_EXP_W      = $clog2(MAX_SAMPLE_JITTER_EXP+1);
localparam LED_SOURCE_W             = 3;
localparam INPUT_SOURCE_W           = 8;

wire [N_PAIR*WINDOW_LENGTH_EXP_W-1:0]   windowLengthExp;
wire [N_PAIR-1:0]                       windowShape;
wire [N_PAIR*SAMPLE_PERIOD_EXP_W-1:0]   samplePeriodExp;
wire [N_PAIR*SAMPLE_JITTER_EXP_W-1:0]   sampleJitterExp;
wire [N_PAIR*LED_SOURCE_W-1:0]          ledSource;
wire [N_PAIR*INPUT_SOURCE_W-1:0]        xSource;
wire [N_PAIR*INPUT_SOURCE_W-1:0]        ySource;

wire [N_PAIR*8-1:0]                     pktfifo_o_data;
wire [N_PAIR-1:0]                       pktfifo_o_empty;
wire [N_PAIR-1:0]                       pktfifo_i_pop;
wire [N_PAIR-1:0]                       pktfifo_i_flush;

wire [N_PAIR*8-1:0]                     jitterSeedByte;
wire [N_PAIR-1:0]                       jitterSeedValid;

bpReg #(
  .N_PAIR                   (N_PAIR),
  .PKTFIFO_DEPTH            (PKTFIFO_DEPTH), // Bytes, not packets.
  .MAX_WINDOW_LENGTH_EXP    (MAX_WINDOW_LENGTH_EXP),
  .WINDOW_PRECISION         (WINDOW_PRECISION),
  .MAX_SAMPLE_PERIOD_EXP    (MAX_SAMPLE_PERIOD_EXP),
  .MAX_SAMPLE_JITTER_EXP    (MAX_SAMPLE_JITTER_EXP)
) u_bpReg (
  .i_clk                  (i_clk),
  .i_rst                  (i_rst),
  .i_cg                   (i_cg),

  .i_pktfifo_data         (pktfifo_o_data),
  .i_pktfifo_empty        (pktfifo_o_empty),
  .o_pktfifo_pop          (pktfifo_i_pop),
  .o_pktfifo_flush        (pktfifo_i_flush),

  .o_reg_windowLengthExp  (windowLengthExp),
  .o_reg_windowShape      (windowShape),
  .o_reg_samplePeriodExp  (samplePeriodExp),
  .o_reg_sampleJitterExp  (sampleJitterExp),
  .o_reg_ledSource        (ledSource),
  .o_reg_xSource          (xSource),
  .o_reg_ySource          (ySource),

  .o_jitterSeedByte       (jitterSeedByte),
  .o_jitterSeedValid      (jitterSeedValid),

  .i_bp_data              (i_bp_data),
  .i_bp_valid             (i_bp_valid),
  .o_bp_ready             (o_bp_ready),

  .o_bp_data              (o_bp_data),
  .o_bp_valid             (o_bp_valid),
  .i_bp_ready             (i_bp_ready)
);


localparam PROBE_SELECT_W = $clog2(N_PROBE);
wire [N_PAIR-1:0] probeX, probeY;
generate for (i = 0; i < N_PAIR; i=i+1) begin
  xbar #(
    .N_IN       (N_PROBE),
    .N_OUT      (2),
    .WIDTH      (1),
    .FF_IN      (1),
    .FF_OUT     (1),
    .FF_SELECT  (0)
  ) u_probeDemux (
    .i_clk        (i_clk),
    .i_cg         (i_cg),

    .i_in         (i_probe),
    .o_out        ({probeY[i],
                    probeX[i]}),
    .i_select     ({ySource[i*PROBE_SELECT_W +: PROBE_SELECT_W],
                    xSource[i*PROBE_SELECT_W +: PROBE_SELECT_W]})
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
    .i_cg                   (i_cg),

    .o_pktfifo_data         (pktfifo_o_data[i*8 +: 8]),
    .o_pktfifo_empty        (pktfifo_o_empty[i]),
    .i_pktfifo_pop          (pktfifo_i_pop[i]),
    .i_pktfifo_flush        (pktfifo_i_flush[i]),

    .i_windowLengthExp      (windowLengthExp[i*WINDOW_LENGTH_EXP_W +: WINDOW_LENGTH_EXP_W]),
    .i_windowShape          (windowShape[i]),
    .i_samplePeriodExp      (samplePeriodExp[i*SAMPLE_PERIOD_EXP_W +: SAMPLE_PERIOD_EXP_W]),
    .i_sampleJitterExp      (sampleJitterExp[i*SAMPLE_JITTER_EXP_W +: SAMPLE_JITTER_EXP_W]),
    .i_ledSource            (ledSource[i*LED_SOURCE_W +: LED_SOURCE_W]),

    .i_jitterSeedByte       (jitterSeedByte[i*8 +: 8]),
    .i_jitterSeedValid      (jitterSeedValid[i]),

    .i_x                    (probeX[i]),
    .i_y                    (probeY[i]),

    .o_ledPwm               (o_ledPwm[i])
  );
end endgenerate

endmodule
