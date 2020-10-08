
module usbfsBpCorrelator #(
  parameter USBFS_VIDPID_SQUAT = 1,
  parameter USBFS_ACM_NOT_GENERIC = 0,
  parameter USBFS_MAX_PKT = 8,  // in {8,16,32,64}. wMaxPacketSize
  parameter MAX_WINDOW_LENGTH_EXP = 16,
  parameter MAX_SAMPLE_PERIOD_EXP = 15,
  parameter MAX_SAMPLE_JITTER_EXP = 8,
  parameter WINDOW_PRECISION      = 8, // 1 < p <= MAX_WINDOW_LENGTH_EXP
  parameter METRIC_PRECISION      = 16,
  parameter PKTFIFO_DEPTH         = 50
) (
  input  wire                       i_clk_48MHz,
  input  wire                       i_rst,
  input  wire                       i_cg,

  // USB {d+, d-}, output enable.
  input  wire                       i_dp,
  input  wire                       i_dn,
  output wire                       o_dp,
  output wire                       o_dn,
  output wire                       o_oe,


  input  wire                       i_x,
  input  wire                       i_y,

  output wire                       o_ledPwm
);

// USB serial pipeline to/from bpReg
wire [7:0] devToHost_data;
wire       devToHost_valid;
wire       devToHost_ready;
wire [7:0] hostToDev_data;
wire       hostToDev_valid;
wire       hostToDev_ready;

// NOTE: Setting MAX_PKT to 8 will actually *increase* LUT usage as yosys will
// convert all the memories to flops instead of using BRAMs.
usbfsSerial #(
  .VIDPID_SQUAT     (USBFS_VIDPID_SQUAT),
  .ACM_NOT_GENERIC  (USBFS_ACM_NOT_GENERIC),
  .MAX_PKT          (USBFS_MAX_PKT) // in {8,16,32,64}
) u_dev (
  .i_clk_48MHz        (i_clk_48MHz),
  .i_rst              (i_rst),

  // USB {d+, d-}, output enable.
  .i_dp               (i_dp),
  .i_dn               (i_dn),
  .o_dp               (o_dp),
  .o_dn               (o_dn),
  .o_oe               (o_oe),

  .i_devToHost_data   (devToHost_data),
  .i_devToHost_valid  (devToHost_valid),
  .o_devToHost_ready  (devToHost_ready),

  .o_hostToDev_data   (hostToDev_data),
  .o_hostToDev_valid  (hostToDev_valid),
  .i_hostToDev_ready  (hostToDev_ready)
);


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

bpReg #(
  .PKTFIFO_DEPTH            (PKTFIFO_DEPTH), // Bytes, not packets.
  .MAX_WINDOW_LENGTH_EXP    (MAX_WINDOW_LENGTH_EXP),
  .WINDOW_PRECISION         (WINDOW_PRECISION),
  .MAX_SAMPLE_PERIOD_EXP    (MAX_SAMPLE_PERIOD_EXP),
  .MAX_SAMPLE_JITTER_EXP    (MAX_SAMPLE_JITTER_EXP)
) u_bpReg (
  .i_clk                  (i_clk_48MHz),
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

  .o_jitterSeedByte       (jitterSeedByte),
  .o_jitterSeedValid      (jitterSeedValid),

  .i_bp_data              (hostToDev_data),
  .i_bp_valid             (hostToDev_valid),
  .o_bp_ready             (hostToDev_ready),

  .o_bp_data              (devToHost_data),
  .o_bp_valid             (devToHost_valid),
  .i_bp_ready             (devToHost_ready)
);


correlator u_correlator (
  .i_clk                  (i_clk_48MHz),
  .i_rst                  (i_rst),
  .i_cg                   (i_cg),

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

  .i_x                    (i_x),
  .i_y                    (i_y),

  .o_ledPwm               (o_ledPwm)
);

endmodule
