`include "dff.vh"
`include "asrt.vh"
`include "misc.vh"

// WIP Correlation Detection
module corrdet #(
  parameter N_EVENTS  = 5,
  parameter N_BSTATES = 4,
  parameter N_NORMALS = 3,
  parameter DATA_W = 8,
  parameter N_MEASUREMENTS_ = N_EVENTS+N_BSTATES*3+N_NORMALS,
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

genvar i;

// {{{ Promote all inputs to same type/size.

wire [DATA_W-1:0] mEvents  [N_EVENTS];
generate for (i=0; i < N_EVENTS; i=i+1) begin : promoteEvents_b
  assign mEvents[i] = {DATA_W{i_events[i]}};
end : promoteEvents_b endgenerate

// bstates imply 3 measurements per input.
//  1. input
//  2. rise
//  3. fall
//
// mBstates contains all implied measurements ordered with falls in the upper
// bits, rises in the middle bits, and inputs in the lower bits:
//  {fallN, ... fall0, riseN, ... rise0, inputN, ... input0}
wire [DATA_W-1:0] mBstates [N_BSTATES*3];
`dff_cg_norst_d(reg [N_BSTATES-1:0], bstates, i_clk, i_cg, i_bstates)
generate for (i=0; i < N_BSTATES*3; i=i+1) begin : promoteBstates_b
  if (i < N_BSTATES)
    assign mBstates[i] = {DATA_W{i_bstates[i-0*N_BSTATES]}};
  else if (i < 2*N_BSTATES)
    assign mBstates[i] = {DATA_W{i_bstates[i-1*N_BSTATES] && !bstates_q[i-1*N_BSTATES]}};
  else
    assign mBstates[i] = {DATA_W{!i_bstates[i-2*N_BSTATES] && bstates_q[i-2*N_BSTATES]}};
end : promoteBstates_b endgenerate

// Combine all input types into one unpacked vector.
localparam EVENT_L = 0;
localparam EVENT_H = N_EVENTS - 1;
localparam BSTATE_L = EVENT_H + 1;
localparam BSTATE_H = BSTATE_L + 3*N_BSTATES - 1;
localparam NORMAL_L = BSTATE_H + 1;
localparam NORMAL_H = NORMAL_L + N_NORMALS - 1;
wire [DATA_W-1:0] measurements [N_MEASUREMENTS_];
generate for (i=0; i < N_MEASUREMENTS_; i=i+1) begin : combineMeasurements_b
  if (EVENT_H >= i)
    assign measurements[i] = mEvents[i - EVENT_L];
  else if (BSTATE_H >= i)
    assign measurements[i] = mBstates[i - BSTATE_L];
  else
    assign measurements[i] = i_normals[DATA_W*(i - NORMAL_L) +: DATA_W];
end : combineMeasurements_b endgenerate

// }}} Promote all inputs to same type/size.

// {{{ Apply windowing function

// TODO: rect
// TODO: logdrop

// }}} Apply windowing function

// {{{ Correlation counters (superset of performance counters)

// TODO: perfcntrs
// TODO: isectcntrs - Intersection, AND
// TODO: sdiffcntrs - Symmetric Difference, XOR

// }}} Correlation counters

// NOTE: Probably don't need CORDIC pipeline if division is all that's used.
// {{{ TODO: CORDIC pipelines for estimators?
/*
The CORDIC Trigonometric Computing" (IRE Transactions Electronic Computers, September 1959)
https://www.drdobbs.com/microcontrollers-cordic-methods/184404244
NOTE: These algorithms are not quite C, and are missing pieces like arctan.

multiply(x, y) {
  for (i=1; i <= B; i++) {
    if (x > 0) {
      x = x - 2^(-i);
      z = z + y*2^(-i);
    } else {
      x = x + 2^(-i);
      z = z - y*2^(-i);
    }
  }
  return(z)
}

divide(x, y) {
  for (i=1; i <= B; i++) {
    if (x > 0) {
       x = x - y*2^(-i);
       z = z + 2^(-i);
    } else {
       x = x + y*2^(-i);
       z = z - 2^(-i);
    }
  }
  return(z)
}

divide_4q(x, y) {
  for (i=1; i <= B; i++) {
    if (x > 0) {
      if (y > 0) {
        x = x - y*2^(-i);
        z = z + 2^(-i);
      } else {
        x = x + y*2^(-i);
        z = z - 2^(-i);
      }
    } else {
      if (y > 0) {
        x = x + y*2^(-i);
        z = z - 2^(-i);
      } else {
        x = x - y*2^(-i);
        z = z + 2^(-i);
      }
    }
  }
  return(z)
}

log10(x) {
  z = 0;
  for (i=1; i <= B; i++) {
    if (x > 1) {
      x = x - x*2^(-i);
      z = z - log10(1-2^(-i));
    } else {
      x = x + x*2^(-i);
      z = z - log10(1+2^(-i));
    }
  }
  return(z)
}

10_to_power(x) {
  z = 1;
  for (i=1; i <= B; i++) {
    if (x > 0)
      x = x - log10(1+2^(-i));
      z = z + z*2^(-i);
    } else {
      x = x - log10(1-2^(-i));
      z = z - z*2^(-i);
    }
  }
  return(z)
}

sin(z) {
   x = 0.6072;
   y = 0;
   for (i=0; i <= B; i++) {
      if (z > 0)
         x = x - y*2^(-i)
         y = y + x*2^(-i)
         z = z - arctan(2^(-i))
      else
         x = x + y*2^(-i)
         y = y - x*2^(-i)
         z = z + arctan(2^(-i))
   }
   return(y)
}

cos(z) {
  x = 0.6072;
  y = 0;
  for (i=0; i <= B; i++) {
    if (z > 0) {
      x = x - y*2^(-i)
      y = y + x*2^(-i)
      z = z - arctan(2^(-i))
    } else {
      x = x + y*2^(-i)
      y = y - x*2^(-i)
      z = z + arctan(2^(-i))
    }
  }
  return(x)
}
*/

// }}} TODO: CORDIC pipelines?

// TODO: estimators.

endmodule
