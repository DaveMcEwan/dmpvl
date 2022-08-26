/* Practical demonstrations from ParameterDatatypes.

A single initial process is used to display the relevant information in the
style of a report.
*/

/* verilator lint_off WIDTH */
module CI
  #(parameter FIVE = 5
  , parameter VEC1D = {32'd1, 32'd2, 32'd3}
  ) ();
endmodule

module CE2
  #(parameter int FIVE = 5
  , parameter bit [2:0][31:0] VEC1D = {32'd1, 32'd2, 32'd3}
  ) ();
endmodule

module CE4
  #(parameter integer FIVE = 5
  , parameter logic [2:0][31:0] VEC1D = {32'd1, 32'd2, 32'd3}
  ) ();
endmodule

`ifndef XCELIUM
// xmvlog: *E,SVVMAP (ParameterDatatypes.sv,*|*): Omitting the assignment to
// constant_param_expression in a param_assignment in a parameter_port_list
// currently is not supported.
module REQ
  #(parameter ANY
  , parameter bit BIT
  , parameter logic LOGIC
  , parameter int INT
  , parameter integer INTEGER
  ) ();
endmodule
`endif
/* verilator lint_on WIDTH */

module parent ();

  typedef struct packed {
    bit b;      // 2-state
    int a;      // 2-state
  } s2;

  typedef struct packed {
    logic b;    // 4-state
    integer a;  // 4-state
  } s4;

  typedef struct packed {
    logic b;    // 4-state
    int a;      // 2-state
  } sM;

  function automatic s2 constantFoo ();
    constantFoo.b = 1'b1;
  endfunction

  function automatic sM constantBaz ();
    constantBaz.b = 1'b1;
  endfunction

  // 2-state constants, good practice.
  localparam s2 FOO_A = {1'b1, 32'd123};
  localparam s2 FOO_B = '1;
  localparam s2 FOO_C = constantFoo();

  // 4-state constants, warrants close inspection.
  localparam s4 BAR_A = {1'bZ, 32'b01XZ}; // Used in a wildcard comparison?
  localparam s4 BAR_B = 'X;               // Legal, but probably nonsense!

  // Accidentally 4-state constants, intended to be 2-state.
  localparam sM BAZ_A = {1'b1, 32'd123};  // All bits are 0 or 1, but 4-state.
  localparam sM BAZ_B = constantBaz();    // Maybe hidden X/Z in here.


  localparam IG_FIVE = 5;
  localparam IG_VEC1D = {32'd111, 32'd222, 32'd333};
  localparam IB_FIVE = "five";
  localparam IB_VEC1D = {11'd7, 22'd8, 33'd9};

  localparam int EG_FIVE = 5;
  localparam bit [2:0][31:0] EG_VEC1D = {32'd111, 32'd222, 32'd333};
  localparam logic [3:0] EB_FIVE = 4'bXZ01;
  localparam logic [2:0][9:0] EB_VEC1D = {10'd111, 10'd222, 10'd333};

  CI #(.FIVE (IG_FIVE), .VEC1D (IG_VEC1D)) u_ci_ig ();
  CI #(.FIVE (EG_FIVE), .VEC1D (EG_VEC1D)) u_ci_eg ();
  CI #(.FIVE (IB_FIVE), .VEC1D (IB_VEC1D)) u_ci_ib ();
  CI #(.FIVE (EB_FIVE), .VEC1D (EB_VEC1D)) u_ci_eb ();

  CE2 #(.FIVE (IG_FIVE), .VEC1D (IG_VEC1D)) u_ce2_ig ();
  CE2 #(.FIVE (EG_FIVE), .VEC1D (EG_VEC1D)) u_ce2_eg ();
  CE2 #(.FIVE (IB_FIVE), .VEC1D (IB_VEC1D)) u_ce2_ib ();
  CE2 #(.FIVE (EB_FIVE), .VEC1D (EB_VEC1D)) u_ce2_eb ();

  CE4 #(.FIVE (IG_FIVE), .VEC1D (IG_VEC1D)) u_ce4_ig ();
  CE4 #(.FIVE (EG_FIVE), .VEC1D (EG_VEC1D)) u_ce4_eg ();
  CE4 #(.FIVE (IB_FIVE), .VEC1D (IB_VEC1D)) u_ce4_ib ();
  CE4 #(.FIVE (EB_FIVE), .VEC1D (EB_VEC1D)) u_ce4_eb ();


  function automatic integer f_myConstant ();
    for (int i=0; i < 32; i++) begin
      case (i % 3)
        0: f_myConstant[i] = 1'b0;
        1: f_myConstant[i] = 1'b1;
        // Woops! Missing arm for i=2?
      endcase
    end
  endfunction

  CE4 #(.FIVE (f_myConstant())) u_ce4_x ();


`ifndef XCELIUM
  REQ
    #(.ANY     (12'd45)
    , .BIT     (1'b0)
    , .LOGIC   (1'bX)
    , .INT     (12'd45)
    , .INTEGER (12'bzx10)
    ) u_req ();
`endif


  localparam logic [1:0] OKAY = 2'b00;
  localparam logic [1:0] WOOPS = 2'bX1;

  logic [1:0] a;
  integer b1, b2;

/* verilator lint_off CASEWITHX */
  always_comb
    case (a)
      OKAY:    b1 = 555;
      WOOPS:   b1 = 666;
      default: b1 = 777;
    endcase
/* verilator lint_on CASEWITHX */

  always_comb
    if (a == OKAY)
      b2 = 555;
    else if (a == WOOPS)
      b2 = 666;
    else
      b2 = 777;

  integer c;
  logic d;
  assign d = (c === 32'd5);


  localparam logic WILDCARD_TRUE1  = 4'b0100 ==? 4'b01XZ;
  localparam logic WILDCARD_TRUE2  = 4'b0111 ==? 4'b01XZ;
  localparam logic WILDCARD_FALSE1 = 4'b1100 ==? 4'b01XZ;
  localparam logic WILDCARD_FALSE2 = 4'b1111 ==? 4'b01XZ;
  localparam logic WILDCARD_XRHS1 = 1'b0 ==? 1'bX;
  localparam logic WILDCARD_XRHS2 = 1'b1 ==? 1'bX;
  localparam logic WILDCARD_XLHS1 = 1'bX ==? 1'b0;
  localparam logic WILDCARD_XLHS2 = 1'bX ==? 1'b1;


  localparam bit PARAMCHECK_ALLGOOD_WILDCARD =
    &{(WILDCARD_TRUE1 === 1'b1)
    , (WILDCARD_TRUE2 === 1'b1)
    , (WILDCARD_FALSE1 === 1'b0)
    , (WILDCARD_FALSE2 === 1'b0)
    , (WILDCARD_XRHS1 === 1'b1)
    , (WILDCARD_XRHS2 === 1'b1)
`ifdef VERILATOR
    // As Verilator is a 2-state tool, where logical equality is equivalent to
    // case equality, the value `1'bX` is treated as `1'b0`.
    , (WILDCARD_XLHS1 === 1'b0)
    , (WILDCARD_XLHS2 === 1'b0)
`else
    , (WILDCARD_XLHS1 === 1'bX)
    , (WILDCARD_XLHS2 === 1'bX)
`endif
    };

  if (!PARAMCHECK_ALLGOOD_WILDCARD) begin: l_paramcheck_allgood_wildcard
    $error("Wildcard operation produced unexpected result.");
    $info("WILDCARD_TRUE1=%b",  WILDCARD_TRUE1);
    $info("WILDCARD_TRUE2=%b",  WILDCARD_TRUE2);
    $info("WILDCARD_FALSE1=%b", WILDCARD_FALSE1);
    $info("WILDCARD_FALSE2=%b", WILDCARD_FALSE2);
    $info("WILDCARD_XRHS1=%b",  WILDCARD_XRHS1);
    $info("WILDCARD_XRHS2=%b",  WILDCARD_XRHS2);
    $info("WILDCARD_XLHS1=%b",  WILDCARD_XLHS1);
    $info("WILDCARD_XLHS2=%b",  WILDCARD_XLHS2);
  end: l_paramcheck_allgood_wildcard


/* verilator lint_off WIDTH */
// Width is mismatched to demonstrate coercion of 96b concatenation to 128b.
localparam bit [3:0][31:0] concatenationA = {32'd1, 32'd2, 32'd333};
localparam bit [127:0] concatenationB = {32'd1, 32'd2, 32'd333};
/* verilator lint_on WIDTH */
localparam bit [2:0][31:0] literalPackedA = '{1, 2, 333};
/* verilator lint_off LITENDIAN */
localparam bit [0:2][31:0] literalPackedB = '{1, 2, 333};
/* verilator lint_on LITENDIAN */
localparam int literalUnpackedA [3] = '{1, 2, 333};
localparam int literalUnpackedB [0:2] = '{1, 2, 333};
localparam int literalUnpackedC [2:0] = '{1, 2, 333};


  integer fd;
  initial begin: l_report
`ifdef QUESTA
    fd = $fopen("QUESTA.rpt");
    $fdisplay(fd, "QUESTA");
`elsif XCELIUM
    fd = $fopen("XCELIUM.rpt");
    $fdisplay(fd, "XCELIUM");
`elsif VERILATOR
    fd = $fopen("VERILATOR.rpt");
    $fdisplay(fd, "VERILATOR");
`else
    fd = $fopen("OTHER.rpt");
    $fdisplay(fd, "OTHER");
`endif

    $fdisplay(fd, "");
    $fdisplay(fd, "Packed Structures With Mixed 2/4-state Members"); // {{{
    $fdisplay(fd, "s2");
    $fdisplay(fd, "  $typename(s2)=%s", $typename(s2));
    $fdisplay(fd, "  $size(s2)=%0d", $size(s2));
    $fdisplay(fd, "s4");
    $fdisplay(fd, "  $typename(s4)=%s", $typename(s4));
    $fdisplay(fd, "  $size(s4)=%0d", $size(s4));
    $fdisplay(fd, "sM");
    $fdisplay(fd, "  $typename(sM)=%s", $typename(sM));
    $fdisplay(fd, "  $size(sM)=%0d", $size(sM));
    $fdisplay(fd, "FOO_A");
    $fdisplay(fd, "  $typename(FOO_A)=%s", $typename(FOO_A));
    $fdisplay(fd, "  $size(FOO_A)=%0d", $size(FOO_A));
    $fdisplay(fd, "  FOO_A=%b", FOO_A);
    $fdisplay(fd, "FOO_B");
    $fdisplay(fd, "  $typename(FOO_B)=%s", $typename(FOO_B));
    $fdisplay(fd, "  $size(FOO_B)=%0d", $size(FOO_B));
    $fdisplay(fd, "  FOO_B=%b", FOO_B);
    $fdisplay(fd, "FOO_C");
    $fdisplay(fd, "  $typename(FOO_C)=%s", $typename(FOO_C));
    $fdisplay(fd, "  $size(FOO_C)=%0d", $size(FOO_C));
    $fdisplay(fd, "  FOO_C=%b", FOO_C);
    $fdisplay(fd, "BAR_A");
    $fdisplay(fd, "  $typename(BAR_A)=%s", $typename(BAR_A));
    $fdisplay(fd, "  $size(BAR_A)=%0d", $size(BAR_A));
    $fdisplay(fd, "  BAR_A=%b", BAR_A);
    $fdisplay(fd, "BAR_B");
    $fdisplay(fd, "  $typename(BAR_B)=%s", $typename(BAR_B));
    $fdisplay(fd, "  $size(BAR_B)=%0d", $size(BAR_B));
    $fdisplay(fd, "  BAR_B=%b", BAR_B);
    $fdisplay(fd, "BAZ_A");
    $fdisplay(fd, "  $typename(BAZ_A)=%s", $typename(BAZ_A));
    $fdisplay(fd, "  $size(BAZ_A)=%0d", $size(BAZ_A));
    $fdisplay(fd, "  BAZ_A=%b", BAZ_A);
    $fdisplay(fd, "BAZ_B");
    $fdisplay(fd, "  $typename(BAZ_B)=%s", $typename(BAZ_B));
    $fdisplay(fd, "  $size(BAZ_B)=%0d", $size(BAZ_B));
    $fdisplay(fd, "  BAZ_B=%b", BAZ_B);
    // }}} Packed Structures With Mixed 2/4-state Members

    $fdisplay(fd, "");
    $fdisplay(fd, "Implicit/Explicit Good/Bad Override Values"); // {{{
    $fdisplay(fd, "IG_FIVE");
    $fdisplay(fd, "  $typename(IG_FIVE)=%s", $typename(IG_FIVE));
    $fdisplay(fd, "  $size(IG_FIVE)=%0d", $size(IG_FIVE));
    $fdisplay(fd, "  IG_FIVE=%b", IG_FIVE);
    $fdisplay(fd, "IG_VEC1D");
    $fdisplay(fd, "  $typename(IG_VEC1D)=%s", $typename(IG_VEC1D));
    $fdisplay(fd, "  $size(IG_VEC1D)=%0d", $size(IG_VEC1D));
    $fdisplay(fd, "  IG_VEC1D=%b", IG_VEC1D);
    $fdisplay(fd, "IB_FIVE");
    $fdisplay(fd, "  $typename(IB_FIVE)=%s", $typename(IB_FIVE));
    $fdisplay(fd, "  $size(IB_FIVE)=%0d", $size(IB_FIVE));
    $fdisplay(fd, "  IB_FIVE=%b", IB_FIVE);
    $fdisplay(fd, "IB_VEC1D");
    $fdisplay(fd, "  $typename(IB_VEC1D)=%s", $typename(IB_VEC1D));
    $fdisplay(fd, "  $size(IB_VEC1D)=%0d", $size(IB_VEC1D));
    $fdisplay(fd, "  IB_VEC1D=%b", IB_VEC1D);
    $fdisplay(fd, "EG_FIVE");
    $fdisplay(fd, "  $typename(EG_FIVE)=%s", $typename(EG_FIVE));
    $fdisplay(fd, "  $size(EG_FIVE)=%0d", $size(EG_FIVE));
    $fdisplay(fd, "  EG_FIVE=%b", EG_FIVE);
    $fdisplay(fd, "EG_VEC1D");
    $fdisplay(fd, "  $typename(EG_VEC1D)=%s", $typename(EG_VEC1D));
    $fdisplay(fd, "  $size(EG_VEC1D)=%0d", $size(EG_VEC1D));
    $fdisplay(fd, "  EG_VEC1D=%b", EG_VEC1D);
    $fdisplay(fd, "EB_FIVE");
    $fdisplay(fd, "  $typename(EB_FIVE)=%s", $typename(EB_FIVE));
    $fdisplay(fd, "  $size(EB_FIVE)=%0d", $size(EB_FIVE));
    $fdisplay(fd, "  EB_FIVE=%b", EB_FIVE);
    $fdisplay(fd, "EB_VEC1D");
    $fdisplay(fd, "  $typename(EB_VEC1D)=%s", $typename(EB_VEC1D));
    $fdisplay(fd, "  $size(EB_VEC1D)=%0d", $size(EB_VEC1D));
    $fdisplay(fd, "  EB_VEC1D=%b", EB_VEC1D);
    // }}} Implicit/Explicit Good/Bad Override Values

    $fdisplay(fd, "");
    $fdisplay(fd, "Overridden Child Module Parameters");
    $fdisplay(fd, "CI"); // {{{
    $fdisplay(fd, "  u_ci_ig");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ci_ig.FIVE)=%s", $typename(u_ci_ig.FIVE));
    $fdisplay(fd, "      $size(u_ci_ig.FIVE)=%0d", $size(u_ci_ig.FIVE));
    $fdisplay(fd, "      u_ci_ig.FIVE=%b", u_ci_ig.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ci_ig.FIVE[2])=%s", $typename(u_ci_ig.FIVE[2]));
    $fdisplay(fd, "      $size(u_ci_ig.FIVE[2])=%0d", $size(u_ci_ig.FIVE[2]));
    $fdisplay(fd, "      u_ci_ig.FIVE[2]=%b", u_ci_ig.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ci_ig.VEC1D)=%s", $typename(u_ci_ig.VEC1D));
    $fdisplay(fd, "      $size(u_ci_ig.VEC1D)=%0d", $size(u_ci_ig.VEC1D));
    $fdisplay(fd, "      u_ci_ig.VEC1D=%b", u_ci_ig.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ci_ig.VEC1D[1])=%s", $typename(u_ci_ig.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ci_ig.VEC1D[1])=%0d", $size(u_ci_ig.VEC1D[1]));
    $fdisplay(fd, "      u_ci_ig.VEC1D[1]=%b", u_ci_ig.VEC1D[1]);
    $fdisplay(fd, "  u_ci_eg");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ci_eg.FIVE)=%s", $typename(u_ci_eg.FIVE));
    $fdisplay(fd, "      $size(u_ci_eg.FIVE)=%0d", $size(u_ci_eg.FIVE));
    $fdisplay(fd, "      u_ci_eg.FIVE=%b", u_ci_eg.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ci_eg.FIVE[2])=%s", $typename(u_ci_eg.FIVE[2]));
    $fdisplay(fd, "      $size(u_ci_eg.FIVE[2])=%0d", $size(u_ci_eg.FIVE[2]));
    $fdisplay(fd, "      u_ci_eg.FIVE[2]=%b", u_ci_eg.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ci_eg.VEC1D)=%s", $typename(u_ci_eg.VEC1D));
    $fdisplay(fd, "      $size(u_ci_eg.VEC1D)=%0d", $size(u_ci_eg.VEC1D));
    $fdisplay(fd, "      u_ci_eg.VEC1D=%b", u_ci_eg.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ci_eg.VEC1D[1])=%s", $typename(u_ci_eg.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ci_eg.VEC1D[1])=%0d", $size(u_ci_eg.VEC1D[1]));
    $fdisplay(fd, "      u_ci_eg.VEC1D[1]=%b", u_ci_eg.VEC1D[1]);
    $fdisplay(fd, "  u_ci_ib");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ci_ib.FIVE)=%s", $typename(u_ci_ib.FIVE));
    $fdisplay(fd, "      $size(u_ci_ib.FIVE)=%0d", $size(u_ci_ib.FIVE));
    $fdisplay(fd, "      u_ci_ib.FIVE=%b", u_ci_ib.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ci_ib.FIVE[2])=%s", $typename(u_ci_ib.FIVE[2]));
    $fdisplay(fd, "      $size(u_ci_ib.FIVE[2])=%0d", $size(u_ci_ib.FIVE[2]));
    $fdisplay(fd, "      u_ci_ib.FIVE[2]=%b", u_ci_ib.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ci_ib.VEC1D)=%s", $typename(u_ci_ib.VEC1D));
    $fdisplay(fd, "      $size(u_ci_ib.VEC1D)=%0d", $size(u_ci_ib.VEC1D));
    $fdisplay(fd, "      u_ci_ib.VEC1D=%b", u_ci_ib.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ci_ib.VEC1D[1])=%s", $typename(u_ci_ib.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ci_ib.VEC1D[1])=%0d", $size(u_ci_ib.VEC1D[1]));
    $fdisplay(fd, "      u_ci_ib.VEC1D[1]=%b", u_ci_ib.VEC1D[1]);
    $fdisplay(fd, "  u_ci_eb");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ci_eb.FIVE)=%s", $typename(u_ci_eb.FIVE));
    $fdisplay(fd, "      $size(u_ci_eb.FIVE)=%0d", $size(u_ci_eb.FIVE));
    $fdisplay(fd, "      u_ci_eb.FIVE=%b", u_ci_eb.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ci_eb.FIVE[2])=%s", $typename(u_ci_eb.FIVE[2]));
    $fdisplay(fd, "      $size(u_ci_eb.FIVE[2])=%0d", $size(u_ci_eb.FIVE[2]));
    $fdisplay(fd, "      u_ci_eb.FIVE[2]=%b", u_ci_eb.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ci_eb.VEC1D)=%s", $typename(u_ci_eb.VEC1D));
    $fdisplay(fd, "      $size(u_ci_eb.VEC1D)=%0d", $size(u_ci_eb.VEC1D));
    $fdisplay(fd, "      u_ci_eb.VEC1D=%b", u_ci_eb.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ci_eb.VEC1D[1])=%s", $typename(u_ci_eb.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ci_eb.VEC1D[1])=%0d", $size(u_ci_eb.VEC1D[1]));
    $fdisplay(fd, "      u_ci_eb.VEC1D[1]=%b", u_ci_eb.VEC1D[1]);
    // }}} CI
    $fdisplay(fd, "CE2"); // {{{
    $fdisplay(fd, "  u_ce2_ig");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ce2_ig.FIVE)=%s", $typename(u_ce2_ig.FIVE));
    $fdisplay(fd, "      $size(u_ce2_ig.FIVE)=%0d", $size(u_ce2_ig.FIVE));
    $fdisplay(fd, "      u_ce2_ig.FIVE=%b", u_ce2_ig.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ce2_ig.FIVE[2])=%s", $typename(u_ce2_ig.FIVE[2]));
    $fdisplay(fd, "      $size(u_ce2_ig.FIVE[2])=%0d", $size(u_ce2_ig.FIVE[2]));
    $fdisplay(fd, "      u_ce2_ig.FIVE[2]=%b", u_ce2_ig.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ce2_ig.VEC1D)=%s", $typename(u_ce2_ig.VEC1D));
    $fdisplay(fd, "      $size(u_ce2_ig.VEC1D)=%0d", $size(u_ce2_ig.VEC1D));
    $fdisplay(fd, "      u_ce2_ig.VEC1D=%b", u_ce2_ig.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ce2_ig.VEC1D[1])=%s", $typename(u_ce2_ig.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ce2_ig.VEC1D[1])=%0d", $size(u_ce2_ig.VEC1D[1]));
    $fdisplay(fd, "      u_ce2_ig.VEC1D[1]=%0d", u_ce2_ig.VEC1D[1]);
    $fdisplay(fd, "  u_ce2_eg");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ce2_eg.FIVE)=%s", $typename(u_ce2_eg.FIVE));
    $fdisplay(fd, "      $size(u_ce2_eg.FIVE)=%0d", $size(u_ce2_eg.FIVE));
    $fdisplay(fd, "      u_ce2_eg.FIVE=%b", u_ce2_eg.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ce2_eg.FIVE[2])=%s", $typename(u_ce2_eg.FIVE[2]));
    $fdisplay(fd, "      $size(u_ce2_eg.FIVE[2])=%0d", $size(u_ce2_eg.FIVE[2]));
    $fdisplay(fd, "      u_ce2_eg.FIVE[2]=%b", u_ce2_eg.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ce2_eg.VEC1D)=%s", $typename(u_ce2_eg.VEC1D));
    $fdisplay(fd, "      $size(u_ce2_eg.VEC1D)=%0d", $size(u_ce2_eg.VEC1D));
    $fdisplay(fd, "      u_ce2_eg.VEC1D=%b", u_ce2_eg.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ce2_eg.VEC1D[1])=%s", $typename(u_ce2_eg.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ce2_eg.VEC1D[1])=%0d", $size(u_ce2_eg.VEC1D[1]));
    $fdisplay(fd, "      u_ce2_eg.VEC1D[1]=%0d", u_ce2_eg.VEC1D[1]);
    $fdisplay(fd, "  u_ce2_ib");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ce2_ib.FIVE)=%s", $typename(u_ce2_ib.FIVE));
    $fdisplay(fd, "      $size(u_ce2_ib.FIVE)=%0d", $size(u_ce2_ib.FIVE));
    $fdisplay(fd, "      u_ce2_ib.FIVE=%b", u_ce2_ib.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ce2_ib.FIVE[2])=%s", $typename(u_ce2_ib.FIVE[2]));
    $fdisplay(fd, "      $size(u_ce2_ib.FIVE[2])=%0d", $size(u_ce2_ib.FIVE[2]));
    $fdisplay(fd, "      u_ce2_ib.FIVE[2]=%b", u_ce2_ib.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ce2_ib.VEC1D)=%s", $typename(u_ce2_ib.VEC1D));
    $fdisplay(fd, "      $size(u_ce2_ib.VEC1D)=%0d", $size(u_ce2_ib.VEC1D));
    $fdisplay(fd, "      u_ce2_ib.VEC1D=%b", u_ce2_ib.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ce2_ib.VEC1D[1])=%s", $typename(u_ce2_ib.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ce2_ib.VEC1D[1])=%0d", $size(u_ce2_ib.VEC1D[1]));
    $fdisplay(fd, "      u_ce2_ib.VEC1D[1]=0x%h", u_ce2_ib.VEC1D[1]);
    $fdisplay(fd, "  u_ce2_eb");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ce2_eb.FIVE)=%s", $typename(u_ce2_eb.FIVE));
    $fdisplay(fd, "      $size(u_ce2_eb.FIVE)=%0d", $size(u_ce2_eb.FIVE));
    $fdisplay(fd, "      u_ce2_eb.FIVE=%b", u_ce2_eb.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ce2_eb.FIVE[2])=%s", $typename(u_ce2_eb.FIVE[2]));
    $fdisplay(fd, "      $size(u_ce2_eb.FIVE[2])=%0d", $size(u_ce2_eb.FIVE[2]));
    $fdisplay(fd, "      u_ce2_eb.FIVE[2]=%b", u_ce2_eb.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ce2_eb.VEC1D)=%s", $typename(u_ce2_eb.VEC1D));
    $fdisplay(fd, "      $size(u_ce2_eb.VEC1D)=%0d", $size(u_ce2_eb.VEC1D));
    $fdisplay(fd, "      u_ce2_eb.VEC1D=%b", u_ce2_eb.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ce2_eb.VEC1D[1])=%s", $typename(u_ce2_eb.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ce2_eb.VEC1D[1])=%0d", $size(u_ce2_eb.VEC1D[1]));
    $fdisplay(fd, "      u_ce2_eb.VEC1D[1]=%0d", u_ce2_eb.VEC1D[1]);
    // }}} CE2
    $fdisplay(fd, "CE4"); // {{{
    $fdisplay(fd, "  u_ce4_ig");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ce4_ig.FIVE)=%s", $typename(u_ce4_ig.FIVE));
    $fdisplay(fd, "      $size(u_ce4_ig.FIVE)=%0d", $size(u_ce4_ig.FIVE));
    $fdisplay(fd, "      u_ce4_ig.FIVE=%b", u_ce4_ig.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ce4_ig.FIVE[2])=%s", $typename(u_ce4_ig.FIVE[2]));
    $fdisplay(fd, "      $size(u_ce4_ig.FIVE[2])=%0d", $size(u_ce4_ig.FIVE[2]));
    $fdisplay(fd, "      u_ce4_ig.FIVE[2]=%b", u_ce4_ig.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ce4_ig.VEC1D)=%s", $typename(u_ce4_ig.VEC1D));
    $fdisplay(fd, "      $size(u_ce4_ig.VEC1D)=%0d", $size(u_ce4_ig.VEC1D));
    $fdisplay(fd, "      u_ce4_ig.VEC1D=%b", u_ce4_ig.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ce4_ig.VEC1D[1])=%s", $typename(u_ce4_ig.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ce4_ig.VEC1D[1])=%0d", $size(u_ce4_ig.VEC1D[1]));
    $fdisplay(fd, "      u_ce4_ig.VEC1D[1]=%0d", u_ce4_ig.VEC1D[1]);
    $fdisplay(fd, "  u_ce4_eg");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ce4_eg.FIVE)=%s", $typename(u_ce4_eg.FIVE));
    $fdisplay(fd, "      $size(u_ce4_eg.FIVE)=%0d", $size(u_ce4_eg.FIVE));
    $fdisplay(fd, "      u_ce4_eg.FIVE=%b", u_ce4_eg.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ce4_eg.FIVE[2])=%s", $typename(u_ce4_eg.FIVE[2]));
    $fdisplay(fd, "      $size(u_ce4_eg.FIVE[2])=%0d", $size(u_ce4_eg.FIVE[2]));
    $fdisplay(fd, "      u_ce4_eg.FIVE[2]=%b", u_ce4_eg.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ce4_eg.VEC1D)=%s", $typename(u_ce4_eg.VEC1D));
    $fdisplay(fd, "      $size(u_ce4_eg.VEC1D)=%0d", $size(u_ce4_eg.VEC1D));
    $fdisplay(fd, "      u_ce4_eg.VEC1D=%b", u_ce4_eg.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ce4_eg.VEC1D[1])=%s", $typename(u_ce4_eg.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ce4_eg.VEC1D[1])=%0d", $size(u_ce4_eg.VEC1D[1]));
    $fdisplay(fd, "      u_ce4_eg.VEC1D[1]=%0d", u_ce4_eg.VEC1D[1]);
    $fdisplay(fd, "  u_ce4_ib");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ce4_ib.FIVE)=%s", $typename(u_ce4_ib.FIVE));
    $fdisplay(fd, "      $size(u_ce4_ib.FIVE)=%0d", $size(u_ce4_ib.FIVE));
    $fdisplay(fd, "      u_ce4_ib.FIVE=%b", u_ce4_ib.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ce4_ib.FIVE[2])=%s", $typename(u_ce4_ib.FIVE[2]));
    $fdisplay(fd, "      $size(u_ce4_ib.FIVE[2])=%0d", $size(u_ce4_ib.FIVE[2]));
    $fdisplay(fd, "      u_ce4_ib.FIVE[2]=%b", u_ce4_ib.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ce4_ib.VEC1D)=%s", $typename(u_ce4_ib.VEC1D));
    $fdisplay(fd, "      $size(u_ce4_ib.VEC1D)=%0d", $size(u_ce4_ib.VEC1D));
    $fdisplay(fd, "      u_ce4_ib.VEC1D=%b", u_ce4_ib.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ce4_ib.VEC1D[1])=%s", $typename(u_ce4_ib.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ce4_ib.VEC1D[1])=%0d", $size(u_ce4_ib.VEC1D[1]));
    $fdisplay(fd, "      u_ce4_ib.VEC1D[1]=%0d", u_ce4_ib.VEC1D[1]);
    $fdisplay(fd, "  u_ce4_eb");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ce4_eb.FIVE)=%s", $typename(u_ce4_eb.FIVE));
    $fdisplay(fd, "      $size(u_ce4_eb.FIVE)=%0d", $size(u_ce4_eb.FIVE));
    $fdisplay(fd, "      u_ce4_eb.FIVE=%b", u_ce4_eb.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ce4_eb.FIVE[2])=%s", $typename(u_ce4_eb.FIVE[2]));
    $fdisplay(fd, "      $size(u_ce4_eb.FIVE[2])=%0d", $size(u_ce4_eb.FIVE[2]));
    $fdisplay(fd, "      u_ce4_eb.FIVE[2]=%b", u_ce4_eb.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ce4_eb.VEC1D)=%s", $typename(u_ce4_eb.VEC1D));
    $fdisplay(fd, "      $size(u_ce4_eb.VEC1D)=%0d", $size(u_ce4_eb.VEC1D));
    $fdisplay(fd, "      u_ce4_eb.VEC1D=%b", u_ce4_eb.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ce4_eb.VEC1D[1])=%s", $typename(u_ce4_eb.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ce4_eb.VEC1D[1])=%0d", $size(u_ce4_eb.VEC1D[1]));
    $fdisplay(fd, "      u_ce4_eb.VEC1D[1]=%b", u_ce4_eb.VEC1D[1]);
    $fdisplay(fd, "  u_ce4_x");
    $fdisplay(fd, "    FIVE");
    $fdisplay(fd, "      $typename(u_ce4_x.FIVE)=%s", $typename(u_ce4_x.FIVE));
    $fdisplay(fd, "      $size(u_ce4_x.FIVE)=%0d", $size(u_ce4_x.FIVE));
    $fdisplay(fd, "      u_ce4_x.FIVE=%b", u_ce4_x.FIVE);
    $fdisplay(fd, "    FIVE[2]");
    $fdisplay(fd, "      $typename(u_ce4_x.FIVE[2])=%s", $typename(u_ce4_x.FIVE[2]));
    $fdisplay(fd, "      $size(u_ce4_x.FIVE[2])=%0d", $size(u_ce4_x.FIVE[2]));
    $fdisplay(fd, "      u_ce4_x.FIVE[2]=%b", u_ce4_x.FIVE[2]);
    $fdisplay(fd, "    VEC1D");
    $fdisplay(fd, "      $typename(u_ce4_x.VEC1D)=%s", $typename(u_ce4_x.VEC1D));
    $fdisplay(fd, "      $size(u_ce4_x.VEC1D)=%0d", $size(u_ce4_x.VEC1D));
    $fdisplay(fd, "      u_ce4_x.VEC1D=%b", u_ce4_x.VEC1D);
    $fdisplay(fd, "    VEC1D[1]");
    $fdisplay(fd, "      $typename(u_ce4_x.VEC1D[1])=%s", $typename(u_ce4_x.VEC1D[1]));
    $fdisplay(fd, "      $size(u_ce4_x.VEC1D[1])=%0d", $size(u_ce4_x.VEC1D[1]));
    $fdisplay(fd, "      u_ce4_x.VEC1D[1]=%b", u_ce4_x.VEC1D[1]);
    // }}} // CE4
`ifndef XCELIUM
    $fdisplay(fd, "REQ"); // {{{
    $fdisplay(fd, "  u_req");
    $fdisplay(fd, "    ANY");
    $fdisplay(fd, "      $typename(u_req.ANY)=%s", $typename(u_req.ANY));
    $fdisplay(fd, "      $size(u_req.ANY)=%0d", $size(u_req.ANY));
    $fdisplay(fd, "      u_req.ANY=%b", u_req.ANY);
    $fdisplay(fd, "    BIT");
    $fdisplay(fd, "      $typename(u_req.BIT)=%s", $typename(u_req.BIT));
    $fdisplay(fd, "      $size(u_req.BIT)=%0d", $size(u_req.BIT));
    $fdisplay(fd, "      u_req.BIT=%b", u_req.BIT);
    $fdisplay(fd, "    LOGIC");
    $fdisplay(fd, "      $typename(u_req.LOGIC)=%s", $typename(u_req.LOGIC));
    $fdisplay(fd, "      $size(u_req.LOGIC)=%0d", $size(u_req.LOGIC));
    $fdisplay(fd, "      u_req.LOGIC=%b", u_req.LOGIC);
    $fdisplay(fd, "    INT");
    $fdisplay(fd, "      $typename(u_req.INT)=%s", $typename(u_req.INT));
    $fdisplay(fd, "      $size(u_req.INT)=%0d", $size(u_req.INT));
    $fdisplay(fd, "      u_req.INT=%b", u_req.INT);
    $fdisplay(fd, "    INTEGER");
    $fdisplay(fd, "      $typename(u_req.INTEGER)=%s", $typename(u_req.INTEGER));
    $fdisplay(fd, "      $size(u_req.INTEGER)=%0d", $size(u_req.INTEGER));
    $fdisplay(fd, "      u_req.INTEGER=%b", u_req.INTEGER);
    // }}} // REQ
`endif

    $fdisplay(fd, "");
    $fdisplay(fd, "Case Equality Synthesis/Simulation Mismatch");
/* verilator lint_off STMTDLY */
    c = 32'b0101; #1;
    $fdisplay(fd, "c=%b d=%b", c, d);
    c = 32'b0xxx; #1;
    $fdisplay(fd, "c=%b d=%b", c, d);
    c = 32'bx101; #1;
    $fdisplay(fd, "c=%b d=%b", c, d);
/* verilator lint_on STMTDLY */

    $fdisplay(fd, "");
    $fdisplay(fd, "Condition Equalities In If/Else vs Case");
/* verilator lint_off STMTDLY */
    a = 2'bXX; #1;
    $fdisplay(fd, "a=%b b1=%0d b2=%0d", a, b1, b2);
    a = 2'b00; #1;
    $fdisplay(fd, "a=%b b1=%0d b2=%0d", a, b1, b2);
    a = 2'b01; #1;
    $fdisplay(fd, "a=%b b1=%0d b2=%0d", a, b1, b2);
    a = 2'bX1; #1;
    $fdisplay(fd, "a=%b b1=%0d b2=%0d", a, b1, b2);
    a = 2'b11; #1;
    $fdisplay(fd, "a=%b b1=%0d b2=%0d", a, b1, b2);
/* verilator lint_on STMTDLY */

    $fdisplay(fd, "");
    $fdisplay(fd, "Wildcard Equality"); // {{{
    $fdisplay(fd, "WILDCARD_TRUE1=(4'b0100 ==? 4'b01XZ)=%b", (4'b0100 ==? 4'b01XZ));
    $fdisplay(fd, "WILDCARD_TRUE2=(4'b0111 ==? 4'b01XZ)=%b", (4'b0111 ==? 4'b01XZ));
    $fdisplay(fd, "WILDCARD_FALSE1=(4'b1100 ==? 4'b01XZ)=%b", (4'b1100 ==? 4'b01XZ));
    $fdisplay(fd, "WILDCARD_FALSE2=(4'b1111 ==? 4'b01XZ)=%b", (4'b1111 ==? 4'b01XZ));
    $fdisplay(fd, "WILDCARD_XRHS1=(1'b0 ==? 1'bX)=%b", (1'b0 ==? 1'bX));
    $fdisplay(fd, "WILDCARD_XRHS2=(1'b1 ==? 1'bX)=%b", (1'b1 ==? 1'bX));
    $fdisplay(fd, "WILDCARD_XLHS1=(1'bX ==? 1'b0)=%b", (1'bX ==? 1'b0));
    $fdisplay(fd, "WILDCARD_XLHS2=(1'bX ==? 1'b1)=%b", (1'bX ==? 1'b1));
    // }}} Wildcard Equality

    $fdisplay(fd, "");
    $fdisplay(fd, "Different Use of Braces");
    $fdisplay(fd, "Concatenation: {4'hA, 4'h5}=0x%h",
      {4'hA, 4'h5}
    );
    $fdisplay(fd, "Streaming concatenation: {<< 4 {16'hABCD}}=0x%h",
      shortint'({<< 4 {16'hABCD}})
    );
    $fdisplay(fd, "Replication: {3{4'hA}}=0x%h",
      {3{4'hA}}
    );
    $fdisplay(fd, "Set membership: (3 inside {1, 2, 3})=%b",
      (3 inside {1, 2, 3})
    );

    $fdisplay(fd, "");
    $fdisplay(fd, "Concatenation vs Array Assignment Patterns");
    $fdisplay(fd, "concatenationA $size(concatenationA)=%0d", $size(concatenationA));
    $fdisplay(fd, "  [0]=%0d [1]=%0d [2]=%0d [3]=%0d", concatenationA[0], concatenationA[1], concatenationA[2], concatenationA[3]);
    $fdisplay(fd, "concatenationB $size(concatenationB)=%0d", $size(concatenationB));
    $fdisplay(fd, "  =0x%h", concatenationB);
    $fdisplay(fd, "literalPackedA $size(literalPackedA)=%0d", $size(literalPackedA));
    $fdisplay(fd, "  [0]=%0d [1]=%0d [2]=%0d", literalPackedA[0], literalPackedA[1], literalPackedA[2]);
    $fdisplay(fd, "literalPackedB $size(literalPackedB)=%0d", $size(literalPackedB));
    $fdisplay(fd, "  [0]=%0d [1]=%0d [2]=%0d", literalPackedB[0], literalPackedB[1], literalPackedB[2]);
    $fdisplay(fd, "literalUnpackedA $size(literalUnpackedA)=%0d", $size(literalUnpackedA));
    $fdisplay(fd, "  [0]=%0d [1]=%0d [2]=%0d", literalUnpackedA[0], literalUnpackedA[1], literalUnpackedA[2]);
    $fdisplay(fd, "literalUnpackedB $size(literalUnpackedB)=%0d", $size(literalUnpackedB));
    $fdisplay(fd, "  [0]=%0d [1]=%0d [2]=%0d", literalUnpackedB[0], literalUnpackedB[1], literalUnpackedB[2]);
    $fdisplay(fd, "literalUnpackedC $size(literalUnpackedC)=%0d", $size(literalUnpackedC));
    $fdisplay(fd, "  [0]=%0d [1]=%0d [2]=%0d", literalUnpackedC[0], literalUnpackedC[1], literalUnpackedC[2]);

    $fclose(fd);
    $finish();
  end: l_report

endmodule
