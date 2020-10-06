module correlator #(
  parameter MAX_WINDOW_LENGTH_EXP = 16,
  parameter MAX_SAMPLE_PERIOD_EXP = 15,
  parameter MAX_SAMPLE_JITTER_EXP = 8,
  parameter WINDOW_PRECISION      = 8, // 1 < p <= MAX_WINDOW_LENGTH_EXP
  parameter METRIC_PRECISION      = 16,
  parameter PKTFIFO_DEPTH         = 50
) (
  input wire          i_clk,
  input wire          i_rst,
  input wire          i_cg,

  input  wire         i_x,
  input  wire         i_y,

  output wire         o_ledPwm,

  input  wire [7:0]   i_bp_data,
  input  wire         i_bp_valid,
  output wire         o_bp_ready,

  output wire [7:0]   o_bp_data,
  output wire         o_bp_valid,
  input  wire         i_bp_ready
);

endmodule
