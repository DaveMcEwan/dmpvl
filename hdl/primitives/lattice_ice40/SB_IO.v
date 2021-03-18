
// Dummy module just to keep V-erilator lint happy.
module SB_IO #(


  // See Input and Output PinFunction Tables.
  // Default value of PIN_TYPE = 6’000000
  // I.E. an input pad, with the input signal registered.
  parameter PIN_TYPE = 6'b000000,

  // By default, the IO will have NO pull up.
  // This parameter is used only on bank 0, 1, and 2.
  // Ignored when it is placed at bank 3.
  parameter PULLUP = 1'b0,

  // Specify the polarity of all FFs in the IO to be falling edge when
  // NEG_TRIGGER == 1.
  // Default is rising edge.
  parameter NEG_TRIGGER = 1'b0,

  // Other IO standards are supported in bank 3 only:
  // SB_SSTL2_CLASS_2, SB_SSTL2_CLASS_1,
  // SB_SSTL18_FULL, SB_SSTL18_HALF,
  // SB_MDDR10, SB_MDDR8, SB_MDDR4, SB_MDDR2, etc.
  parameter IO_STANDARD = "SB_LVCMOS"
) (
  /* verilator lint_off PINMISSING */
  inout  wire       PACKAGE_PIN,
  input  wire       LATCH_INPUT_VALUE,
  input  wire       CLOCK_ENABLE,
  input  wire       INPUT_CLK,
  input  wire       OUTPUT_CLK,
  input  wire       OUTPUT_ENABLE,
  input  wire       D_OUT_0,
  input  wire       D_OUT_1,
  output wire       D_IN_0,
  output wire       D_IN_1
  /* verilator lint_on PINMISSING */
);

endmodule
