`include "dff.vh"
`include "asrt.vh"
`include "misc.vh"

// WIP Correlation Detection
module corrdet #(
  parameter N_EVENTS  = 5,
  parameter N_BSTATES = 4,
  parameter N_NORMALS = 3,
  parameter DATA_W = 8,
  parameter N_MEASUREMENTS_ = N_EVENTS+N_BSTATES*4+N_NORMALS,
  parameter N_RESULTS_ = N_MEASUREMENTS_*(N_MEASUREMENTS_-1) / 2, // quadratic (m**2 - m) / 2

  parameter WINDOW_LOGDROP = 1,   // Enable logdrop windowing

  parameter CALCULATE_COV = 1,    // Enable Cov calculator
  parameter CALCULATE_DEP = 1,    // Enable Dep calculator
  parameter CALCULATE_HAM = 1,    // Enable Ham calculator
  parameter CALCULATE_TMT = 1,    // Enable Tmt calculator
  parameter CALCULATE_ANN = 1,    // Enable ANN combining calculator

  parameter FIFO_DEPTH = 16
) (
  input  wire                           i_clk,
  input  wire                           i_cg,
  input  wire                           i_rst,

  // User is able to do wrong, weird, and wonderful things but has full flexibility.
  input  wire [31:0]                    i_windowLength,
  input  wire                           i_windowShape, // 0=rect, 1=logdrop

  // Measurements
  input  wire [N_EVENTS-1:0]            i_events,
  input  wire [N_BSTATES-1:0]           i_bstates,
  input  wire [N_NORMALS*DATA_W-1:0]    i_normals,

  // Enable logic from output side rather than input.
  // Gives greater flexability at the cost of larger logic.
  input  wire [N_RESULTS_-1:0]          i_enables,
  input  wire [N_RESULTS_*DATA_W-1:0]   i_thresholds,

  // Pipeline interface to stream results from internal fifo.
  input  wire                           i_resultReady,
  output wire                           o_resultValid,
  output wire [$clog2(N_RESULTS_)-1:0]  o_resultIdx,
  output wire [DATA_W-1:0]              o_resultData,
  output wire                           o_resultArq // Toggle on each window boundary.
);


endmodule
