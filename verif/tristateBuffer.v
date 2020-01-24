
module tristateBuffer (
  // Sink/source select.
  // 0=high impedence, 1=low impedence.
  input  wire   i_outputEnable,

  // Sink from off-chip.
  // Unknown value when i_outputEnable is high.
  output wire   o_xIn,

  // Source from off-chip.
  // Value goes nowhere when i_outputEnable is low.
  input  wire   i_xOut,

  // Bidirectional GPIO pad to/from off-chip.
  inout  wire   b_xIO
);

  assign b_xIO = i_outputEnable ? i_xOut : 1'bz;
  assign o_xIn = i_outputEnable ? 1'b0 : b_xIO;

endmodule
