
module usbfsBpCorrelator #(
  parameter USBFS_VIDPID_SQUAT = 1,
  parameter USBFS_ACM_NOT_GENERIC = 0,
  parameter USBFS_MAX_PKT = 8,  // in {8,16,32,64}. wMaxPacketSize
  parameter N_PROBE               = 4, // 2..64
  parameter N_PAIR                = 2, // 1..8
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


  input  wire [N_PROBE-1:0]         i_probe,

  output wire [N_PAIR-1:0]          o_ledPwm
);

genvar i;

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

bpCorrelator #(
  .N_PROBE                  (N_PROBE),
  .N_PAIR                   (N_PAIR),
  .PKTFIFO_DEPTH            (PKTFIFO_DEPTH), // Bytes, not packets.
  .MAX_WINDOW_LENGTH_EXP    (MAX_WINDOW_LENGTH_EXP),
  .WINDOW_PRECISION         (WINDOW_PRECISION),
  .MAX_SAMPLE_PERIOD_EXP    (MAX_SAMPLE_PERIOD_EXP),
  .MAX_SAMPLE_JITTER_EXP    (MAX_SAMPLE_JITTER_EXP)
) u_bpCorrelator (
  .i_clk                  (i_clk_48MHz),
  .i_rst                  (i_rst),
  .i_cg                   (i_cg),

  .i_bp_data              (hostToDev_data),
  .i_bp_valid             (hostToDev_valid),
  .o_bp_ready             (hostToDev_ready),

  .o_bp_data              (devToHost_data),
  .o_bp_valid             (devToHost_valid),
  .i_bp_ready             (devToHost_ready),

  .i_probe                (i_probe),
  .o_ledPwm               (o_ledPwm)
);

endmodule
