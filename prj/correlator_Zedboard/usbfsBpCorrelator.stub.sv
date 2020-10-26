
module usbfsBpCorrelator #(
  parameter USBFS_VIDPID_SQUAT = 1,
  parameter USBFS_ACM_NOT_GENERIC = 0,
  parameter USBFS_MAX_PKT = 8,  // in {8,16,32,64}. wMaxPacketSize
  parameter N_PROBE               = 4, // 2..256
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

endmodule
