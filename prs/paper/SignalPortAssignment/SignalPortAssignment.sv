/* Practical demonstrations of multi-driven signal ports.

A single initial process is used to display the relevant information in the
style of a report.
*/

`ifdef VERILATOR
`define NO_ASSIGNMENT_TO_INPUT
`define NO_OUTPUT_SHORT
`endif

`ifdef QUESTA
`define INOUT_MUST_BE_NET
`define ILLEGAL_REFERENCE_TO_NET
`define NO_OUTPUT_SHORT
`define NO_MULTI_CONTINUOUS
`define RUNTIME_CONTINUOUS_PROCEDURAL
`endif

`ifdef XCELIUM
`define INOUT_MUST_BE_NET
`define ILLEGAL_REFERENCE_TO_NET
`define MULTIDRIVE_CONFLICT
`define ALWAYSCOMB_UNEVAL_TIME0
`define NO_OUTPUT_SHORT
`endif

module Continuous // {{{
  ( input  logic      i_logic
  , input  var logic  i_var_logic
  , input  tri logic  i_tri_logic
  , input  wire logic i_wire_logic

  , output logic      o_logic
  , output var logic  o_var_logic
  , output tri logic  o_tri_logic
  , output wire logic o_wire_logic

`ifndef INOUT_MUST_BE_NET
  , inout  logic      b_logic
  , inout  var logic  b_var_logic
`endif
  , inout  tri logic  b_tri_logic
  , inout  wire logic b_wire_logic
  );

`ifndef NO_ASSIGNMENT_TO_INPUT
  assign i_logic = 1'b1; // Neither Questa or Xcelium throw error.
`ifndef MULTIDRIVE_CONFLICT
  assign i_var_logic = 1'b1; // Xcelium throws error, but Questa doesn't.
`endif
  assign i_tri_logic = 1'b1;
  assign i_wire_logic = 1'b1;
`endif

  assign o_logic = 1'b1;
  assign o_var_logic = 1'b1;
  assign o_tri_logic = 1'b1;
  assign o_wire_logic = 1'b1;

  assign b_logic = 1'b1; // Warning (not error) undefined signal.
  assign b_var_logic = 1'b1; // Warning (not error) undefined signal.
  assign b_tri_logic = 1'b1;
  assign b_wire_logic = 1'b1;

endmodule // }}} Continuous

module Procedural // {{{
  ( input  logic      i_logic
  , input  var logic  i_var_logic
  , input  tri logic  i_tri_logic
  , input  wire logic i_wire_logic

  , output logic      o_logic
  , output var logic  o_var_logic
  , output tri logic  o_tri_logic
  , output wire logic o_wire_logic

`ifndef INOUT_MUST_BE_NET
  , inout  logic      b_logic
  , inout  var logic  b_var_logic
`endif
  , inout  tri logic  b_tri_logic
  , inout  wire logic b_wire_logic
  );

`ifndef NO_ASSIGNMENT_TO_INPUT
`ifndef ILLEGAL_REFERENCE_TO_NET
  always_comb i_logic = 1'b1;
`endif
`ifndef MULTIDRIVE_CONFLICT
  always_comb i_var_logic = 1'b1;
`endif
`ifndef ILLEGAL_REFERENCE_TO_NET
  always_comb i_tri_logic = 1'b1;
  always_comb i_wire_logic = 1'b1;
`endif
`endif

  always_comb o_logic = 1'b1;
  always_comb o_var_logic = 1'b1;
`ifndef ILLEGAL_REFERENCE_TO_NET
  always_comb o_tri_logic = 1'b1;
  always_comb o_wire_logic = 1'b1;
`endif

`ifndef INOUT_MUST_BE_NET
  always_comb b_logic = 1'b1;
  always_comb b_var_logic = 1'b1;
`endif
`ifndef ILLEGAL_REFERENCE_TO_NET
  always_comb b_tri_logic = 1'b1;
  always_comb b_wire_logic = 1'b1;
`endif

endmodule // }}} Procedural

// All ports on all instances are assigned from within to 1'b1.
// u_internal_* -> All ports unconnected.
// u_external_* -> All ports connected to 1'b0.
module parent (
`ifndef VERILATOR
  input var logic i_clk, i_rst
`endif
);

  Continuous u_internal_continuous // {{{
    ( .i_logic        ()
    , .i_var_logic    ()
    , .i_tri_logic    ()
    , .i_wire_logic   ()

    , .o_logic        ()
    , .o_var_logic    ()
    , .o_tri_logic    ()
    , .o_wire_logic   ()

`ifndef INOUT_MUST_BE_NET
    , .b_logic        ()
    , .b_var_logic    ()
`endif
    , .b_tri_logic    ()
    , .b_wire_logic   ()
    ); // }}}

  Procedural u_internal_procedural // {{{
    ( .i_logic        ()
    , .i_var_logic    ()
    , .i_tri_logic    ()
    , .i_wire_logic   ()

    , .o_logic        ()
    , .o_var_logic    ()
    , .o_tri_logic    ()
    , .o_wire_logic   ()

`ifndef INOUT_MUST_BE_NET
    , .b_logic        ()
    , .b_var_logic    ()
`endif
    , .b_tri_logic    ()
    , .b_wire_logic   ()
    ); // }}}

/* verilator lint_off PINMISSING */
  Continuous u_external_continuous // {{{
    ( .i_logic        (1'b0)
`ifndef NO_MULTI_CONTINUOUS
    , .i_var_logic    (1'b0)
`endif
    , .i_tri_logic    (1'b0)
    , .i_wire_logic   (1'b0)

`ifndef NO_OUTPUT_SHORT
    , .o_logic        (1'b0)
    , .o_var_logic    (1'b0)
    , .o_tri_logic    (1'b0)
    , .o_wire_logic   (1'b0)
`endif

`ifndef NO_OUTPUT_SHORT
    , .b_logic        (1'b0)
    , .b_var_logic    (1'b0)
    , .b_tri_logic    (1'b0)
    , .b_wire_logic   (1'b0)
`endif
    ); // }}}
/* verilator lint_on PINMISSING */

/* verilator lint_off PINMISSING */
  Procedural u_external_procedural // {{{
    ( .i_logic        (1'b0)
`ifndef RUNTIME_CONTINUOUS_PROCEDURAL
    , .i_var_logic    (1'b0)
`endif
    , .i_tri_logic    (1'b0)
    , .i_wire_logic   (1'b0)

`ifndef NO_OUTPUT_SHORT
    , .o_logic        (1'b0)
    , .o_var_logic    (1'b0)
    , .o_tri_logic    (1'b0)
    , .o_wire_logic   (1'b0)
`endif

`ifndef NO_OUTPUT_SHORT
    , .b_logic        (1'b0)
    , .b_var_logic    (1'b0)
    , .b_tri_logic    (1'b0)
    , .b_wire_logic   (1'b0)
`endif
    ); // }}}
/* verilator lint_on PINMISSING */

  integer fd;
  initial begin: l_report
`ifdef QUESTA
    fd = $fopen("QUESTA.rpt");
    $fdisplay(fd, "QUESTA");
`elsif RIVIERA
    fd = $fopen("RIVIERA.rpt");
    $fdisplay(fd, "RIVIERA");
`elsif VCS
    fd = $fopen("VCS.rpt");
    $fdisplay(fd, "VCS");
`elsif XCELIUM
    fd = $fopen("XCELIUM.rpt");
    $fdisplay(fd, "XCELIUM");
`elsif VERILATOR
    fd = $fopen("VERILATOR.rpt");
    $fdisplay(fd, "VERILATOR");
`elsif IVERILOG
    fd = $fopen("IVERILOG.rpt");
    $fdisplay(fd, "IVERILOG");
`else
    fd = $fopen("OTHER.rpt");
    $fdisplay(fd, "OTHER");
`endif

`ifdef ALWAYSCOMB_UNEVAL_TIME0
    #1;
`endif

    $fdisplay(fd, "");
    $fdisplay(fd, "Internal assignments, i.e. within child module"); // {{{
    $fdisplay(fd, " continuous");
    $fdisplay(fd, "  input");
    $fdisplay(fd, "    $typename(u_internal_continuous.i_logic)=%s", $typename(u_internal_continuous.i_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.i_logic)=%0d", $size(u_internal_continuous.i_logic));
    $fdisplay(fd, "    u_internal_continuous.i_logic=%b", u_internal_continuous.i_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_continuous.i_var_logic)=%s", $typename(u_internal_continuous.i_var_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.i_var_logic)=%0d", $size(u_internal_continuous.i_var_logic));
`ifndef MULTIDRIVE_CONFLICT
    $fdisplay(fd, "    u_internal_continuous.i_var_logic=%b", u_internal_continuous.i_var_logic);
`endif
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_continuous.i_tri_logic)=%s", $typename(u_internal_continuous.i_tri_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.i_tri_logic)=%0d", $size(u_internal_continuous.i_tri_logic));
    $fdisplay(fd, "    u_internal_continuous.i_tri_logic=%b", u_internal_continuous.i_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_continuous.i_wire_logic)=%s", $typename(u_internal_continuous.i_wire_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.i_wire_logic)=%0d", $size(u_internal_continuous.i_wire_logic));
    $fdisplay(fd, "    u_internal_continuous.i_wire_logic=%b", u_internal_continuous.i_wire_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "  output");
    $fdisplay(fd, "    $typename(u_internal_continuous.o_logic)=%s", $typename(u_internal_continuous.o_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.o_logic)=%0d", $size(u_internal_continuous.o_logic));
    $fdisplay(fd, "    u_internal_continuous.o_logic=%b", u_internal_continuous.o_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_continuous.o_var_logic)=%s", $typename(u_internal_continuous.o_var_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.o_var_logic)=%0d", $size(u_internal_continuous.o_var_logic));
    $fdisplay(fd, "    u_internal_continuous.o_var_logic=%b", u_internal_continuous.o_var_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_continuous.o_tri_logic)=%s", $typename(u_internal_continuous.o_tri_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.o_tri_logic)=%0d", $size(u_internal_continuous.o_tri_logic));
    $fdisplay(fd, "    u_internal_continuous.o_tri_logic=%b", u_internal_continuous.o_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_continuous.o_wire_logic)=%s", $typename(u_internal_continuous.o_wire_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.o_wire_logic)=%0d", $size(u_internal_continuous.o_wire_logic));
    $fdisplay(fd, "    u_internal_continuous.o_wire_logic=%b", u_internal_continuous.o_wire_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "  inout");
    $fdisplay(fd, "    $typename(u_internal_continuous.b_logic)=%s", $typename(u_internal_continuous.b_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.b_logic)=%0d", $size(u_internal_continuous.b_logic));
    $fdisplay(fd, "    u_internal_continuous.b_logic=%b", u_internal_continuous.b_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_continuous.b_var_logic)=%s", $typename(u_internal_continuous.b_var_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.b_var_logic)=%0d", $size(u_internal_continuous.b_var_logic));
    $fdisplay(fd, "    u_internal_continuous.b_var_logic=%b", u_internal_continuous.b_var_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_continuous.b_tri_logic)=%s", $typename(u_internal_continuous.b_tri_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.b_tri_logic)=%0d", $size(u_internal_continuous.b_tri_logic));
    $fdisplay(fd, "    u_internal_continuous.b_tri_logic=%b", u_internal_continuous.b_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_continuous.b_wire_logic)=%s", $typename(u_internal_continuous.b_wire_logic));
    $fdisplay(fd, "    $size(u_internal_continuous.b_wire_logic)=%0d", $size(u_internal_continuous.b_wire_logic));
    $fdisplay(fd, "    u_internal_continuous.b_wire_logic=%b", u_internal_continuous.b_wire_logic);
    $fdisplay(fd, " procedural");
    $fdisplay(fd, "  input");
    $fdisplay(fd, "    $typename(u_internal_procedural.i_logic)=%s", $typename(u_internal_procedural.i_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.i_logic)=%0d", $size(u_internal_procedural.i_logic));
    $fdisplay(fd, "    u_internal_procedural.i_logic=%b", u_internal_procedural.i_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_procedural.i_var_logic)=%s", $typename(u_internal_procedural.i_var_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.i_var_logic)=%0d", $size(u_internal_procedural.i_var_logic));
`ifndef MULTIDRIVE_CONFLICT
    $fdisplay(fd, "    u_internal_procedural.i_var_logic=%b", u_internal_procedural.i_var_logic);
`endif
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_procedural.i_tri_logic)=%s", $typename(u_internal_procedural.i_tri_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.i_tri_logic)=%0d", $size(u_internal_procedural.i_tri_logic));
    $fdisplay(fd, "    u_internal_procedural.i_tri_logic=%b", u_internal_procedural.i_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_procedural.i_wire_logic)=%s", $typename(u_internal_procedural.i_wire_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.i_wire_logic)=%0d", $size(u_internal_procedural.i_wire_logic));
    $fdisplay(fd, "    u_internal_procedural.i_wire_logic=%b", u_internal_procedural.i_wire_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "  output");
    $fdisplay(fd, "    $typename(u_internal_procedural.o_logic)=%s", $typename(u_internal_procedural.o_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.o_logic)=%0d", $size(u_internal_procedural.o_logic));
    $fdisplay(fd, "    u_internal_procedural.o_logic=%b", u_internal_procedural.o_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_procedural.o_var_logic)=%s", $typename(u_internal_procedural.o_var_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.o_var_logic)=%0d", $size(u_internal_procedural.o_var_logic));
    $fdisplay(fd, "    u_internal_procedural.o_var_logic=%b", u_internal_procedural.o_var_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_procedural.o_tri_logic)=%s", $typename(u_internal_procedural.o_tri_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.o_tri_logic)=%0d", $size(u_internal_procedural.o_tri_logic));
    $fdisplay(fd, "    u_internal_procedural.o_tri_logic=%b", u_internal_procedural.o_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_procedural.o_wire_logic)=%s", $typename(u_internal_procedural.o_wire_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.o_wire_logic)=%0d", $size(u_internal_procedural.o_wire_logic));
    $fdisplay(fd, "    u_internal_procedural.o_wire_logic=%b", u_internal_procedural.o_wire_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "  inout");
`ifndef INOUT_MUST_BE_NET
    $fdisplay(fd, "    $typename(u_internal_procedural.b_logic)=%s", $typename(u_internal_procedural.b_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.b_logic)=%0d", $size(u_internal_procedural.b_logic));
    $fdisplay(fd, "    u_internal_procedural.b_logic=%b", u_internal_procedural.b_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_procedural.b_var_logic)=%s", $typename(u_internal_procedural.b_var_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.b_var_logic)=%0d", $size(u_internal_procedural.b_var_logic));
    $fdisplay(fd, "    u_internal_procedural.b_var_logic=%b", u_internal_procedural.b_var_logic);
    $fdisplay(fd, "");
`endif
    $fdisplay(fd, "    $typename(u_internal_procedural.b_tri_logic)=%s", $typename(u_internal_procedural.b_tri_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.b_tri_logic)=%0d", $size(u_internal_procedural.b_tri_logic));
    $fdisplay(fd, "    u_internal_procedural.b_tri_logic=%b", u_internal_procedural.b_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_internal_procedural.b_wire_logic)=%s", $typename(u_internal_procedural.b_wire_logic));
    $fdisplay(fd, "    $size(u_internal_procedural.b_wire_logic)=%0d", $size(u_internal_procedural.b_wire_logic));
    $fdisplay(fd, "    u_internal_procedural.b_wire_logic=%b", u_internal_procedural.b_wire_logic);
    $fdisplay(fd, "");
    // }}} Internal assignments

    $fdisplay(fd, "");
    $fdisplay(fd, "External assignments, i.e. outwith child module"); // {{{
    $fdisplay(fd, " continuous");
    $fdisplay(fd, "  input");
    $fdisplay(fd, "    $typename(u_external_continuous.i_logic)=%s", $typename(u_external_continuous.i_logic));
    $fdisplay(fd, "    $size(u_external_continuous.i_logic)=%0d", $size(u_external_continuous.i_logic));
    $fdisplay(fd, "    u_external_continuous.i_logic=%b", u_external_continuous.i_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_continuous.i_var_logic)=%s", $typename(u_external_continuous.i_var_logic));
    $fdisplay(fd, "    $size(u_external_continuous.i_var_logic)=%0d", $size(u_external_continuous.i_var_logic));
`ifndef MULTIDRIVE_CONFLICT
    $fdisplay(fd, "    u_external_continuous.i_var_logic=%b", u_external_continuous.i_var_logic);
`endif
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_continuous.i_tri_logic)=%s", $typename(u_external_continuous.i_tri_logic));
    $fdisplay(fd, "    $size(u_external_continuous.i_tri_logic)=%0d", $size(u_external_continuous.i_tri_logic));
    $fdisplay(fd, "    u_external_continuous.i_tri_logic=%b", u_external_continuous.i_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_continuous.i_wire_logic)=%s", $typename(u_external_continuous.i_wire_logic));
    $fdisplay(fd, "    $size(u_external_continuous.i_wire_logic)=%0d", $size(u_external_continuous.i_wire_logic));
    $fdisplay(fd, "    u_external_continuous.i_wire_logic=%b", u_external_continuous.i_wire_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "  output");
    $fdisplay(fd, "    $typename(u_external_continuous.o_logic)=%s", $typename(u_external_continuous.o_logic));
    $fdisplay(fd, "    $size(u_external_continuous.o_logic)=%0d", $size(u_external_continuous.o_logic));
    $fdisplay(fd, "    u_external_continuous.o_logic=%b", u_external_continuous.o_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_continuous.o_var_logic)=%s", $typename(u_external_continuous.o_var_logic));
    $fdisplay(fd, "    $size(u_external_continuous.o_var_logic)=%0d", $size(u_external_continuous.o_var_logic));
    $fdisplay(fd, "    u_external_continuous.o_var_logic=%b", u_external_continuous.o_var_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_continuous.o_tri_logic)=%s", $typename(u_external_continuous.o_tri_logic));
    $fdisplay(fd, "    $size(u_external_continuous.o_tri_logic)=%0d", $size(u_external_continuous.o_tri_logic));
    $fdisplay(fd, "    u_external_continuous.o_tri_logic=%b", u_external_continuous.o_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_continuous.o_wire_logic)=%s", $typename(u_external_continuous.o_wire_logic));
    $fdisplay(fd, "    $size(u_external_continuous.o_wire_logic)=%0d", $size(u_external_continuous.o_wire_logic));
    $fdisplay(fd, "    u_external_continuous.o_wire_logic=%b", u_external_continuous.o_wire_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "  inout");
    $fdisplay(fd, "    $typename(u_external_continuous.b_logic)=%s", $typename(u_external_continuous.b_logic));
    $fdisplay(fd, "    $size(u_external_continuous.b_logic)=%0d", $size(u_external_continuous.b_logic));
    $fdisplay(fd, "    u_external_continuous.b_logic=%b", u_external_continuous.b_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_continuous.b_var_logic)=%s", $typename(u_external_continuous.b_var_logic));
    $fdisplay(fd, "    $size(u_external_continuous.b_var_logic)=%0d", $size(u_external_continuous.b_var_logic));
    $fdisplay(fd, "    u_external_continuous.b_var_logic=%b", u_external_continuous.b_var_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_continuous.b_tri_logic)=%s", $typename(u_external_continuous.b_tri_logic));
    $fdisplay(fd, "    $size(u_external_continuous.b_tri_logic)=%0d", $size(u_external_continuous.b_tri_logic));
    $fdisplay(fd, "    u_external_continuous.b_tri_logic=%b", u_external_continuous.b_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_continuous.b_wire_logic)=%s", $typename(u_external_continuous.b_wire_logic));
    $fdisplay(fd, "    $size(u_external_continuous.b_wire_logic)=%0d", $size(u_external_continuous.b_wire_logic));
    $fdisplay(fd, "    u_external_continuous.b_wire_logic=%b", u_external_continuous.b_wire_logic);
    $fdisplay(fd, " procedural");
    $fdisplay(fd, "  input");
    $fdisplay(fd, "    $typename(u_external_procedural.i_logic)=%s", $typename(u_external_procedural.i_logic));
    $fdisplay(fd, "    $size(u_external_procedural.i_logic)=%0d", $size(u_external_procedural.i_logic));
    $fdisplay(fd, "    u_external_procedural.i_logic=%b", u_external_procedural.i_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_procedural.i_var_logic)=%s", $typename(u_external_procedural.i_var_logic));
    $fdisplay(fd, "    $size(u_external_procedural.i_var_logic)=%0d", $size(u_external_procedural.i_var_logic));
`ifndef MULTIDRIVE_CONFLICT
    $fdisplay(fd, "    u_external_procedural.i_var_logic=%b", u_external_procedural.i_var_logic);
`endif
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_procedural.i_tri_logic)=%s", $typename(u_external_procedural.i_tri_logic));
    $fdisplay(fd, "    $size(u_external_procedural.i_tri_logic)=%0d", $size(u_external_procedural.i_tri_logic));
    $fdisplay(fd, "    u_external_procedural.i_tri_logic=%b", u_external_procedural.i_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_procedural.i_wire_logic)=%s", $typename(u_external_procedural.i_wire_logic));
    $fdisplay(fd, "    $size(u_external_procedural.i_wire_logic)=%0d", $size(u_external_procedural.i_wire_logic));
    $fdisplay(fd, "    u_external_procedural.i_wire_logic=%b", u_external_procedural.i_wire_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "  output");
    $fdisplay(fd, "    $typename(u_external_procedural.o_logic)=%s", $typename(u_external_procedural.o_logic));
    $fdisplay(fd, "    $size(u_external_procedural.o_logic)=%0d", $size(u_external_procedural.o_logic));
    $fdisplay(fd, "    u_external_procedural.o_logic=%b", u_external_procedural.o_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_procedural.o_var_logic)=%s", $typename(u_external_procedural.o_var_logic));
    $fdisplay(fd, "    $size(u_external_procedural.o_var_logic)=%0d", $size(u_external_procedural.o_var_logic));
    $fdisplay(fd, "    u_external_procedural.o_var_logic=%b", u_external_procedural.o_var_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_procedural.o_tri_logic)=%s", $typename(u_external_procedural.o_tri_logic));
    $fdisplay(fd, "    $size(u_external_procedural.o_tri_logic)=%0d", $size(u_external_procedural.o_tri_logic));
    $fdisplay(fd, "    u_external_procedural.o_tri_logic=%b", u_external_procedural.o_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_procedural.o_wire_logic)=%s", $typename(u_external_procedural.o_wire_logic));
    $fdisplay(fd, "    $size(u_external_procedural.o_wire_logic)=%0d", $size(u_external_procedural.o_wire_logic));
    $fdisplay(fd, "    u_external_procedural.o_wire_logic=%b", u_external_procedural.o_wire_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "  inout");
`ifndef INOUT_MUST_BE_NET
    $fdisplay(fd, "    $typename(u_external_procedural.b_logic)=%s", $typename(u_external_procedural.b_logic));
    $fdisplay(fd, "    $size(u_external_procedural.b_logic)=%0d", $size(u_external_procedural.b_logic));
    $fdisplay(fd, "    u_external_procedural.b_logic=%b", u_external_procedural.b_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_procedural.b_var_logic)=%s", $typename(u_external_procedural.b_var_logic));
    $fdisplay(fd, "    $size(u_external_procedural.b_var_logic)=%0d", $size(u_external_procedural.b_var_logic));
    $fdisplay(fd, "    u_external_procedural.b_var_logic=%b", u_external_procedural.b_var_logic);
    $fdisplay(fd, "");
`endif
    $fdisplay(fd, "    $typename(u_external_procedural.b_tri_logic)=%s", $typename(u_external_procedural.b_tri_logic));
    $fdisplay(fd, "    $size(u_external_procedural.b_tri_logic)=%0d", $size(u_external_procedural.b_tri_logic));
    $fdisplay(fd, "    u_external_procedural.b_tri_logic=%b", u_external_procedural.b_tri_logic);
    $fdisplay(fd, "");
    $fdisplay(fd, "    $typename(u_external_procedural.b_wire_logic)=%s", $typename(u_external_procedural.b_wire_logic));
    $fdisplay(fd, "    $size(u_external_procedural.b_wire_logic)=%0d", $size(u_external_procedural.b_wire_logic));
    $fdisplay(fd, "    u_external_procedural.b_wire_logic=%b", u_external_procedural.b_wire_logic);
    $fdisplay(fd, "");
    // }}} External assignments

    $fclose(fd);
    $finish();
  end: l_report

endmodule
