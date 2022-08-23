/* Practical demonstrations from ParameterDatatypes.

A single initial process is used to display the relevant information in the
style of a report.
*/

                                                  /* verilator lint_off WIDTH */
module CI
  #(parameter FIVE = 5
  , parameter VEC1D = {32'd1, 32'd2, 32'd3}
//, parameter NOVALUE                     Commented to avoid need to override.
  ) ();
endmodule

module CE2
  #(parameter int FIVE = 5
  , parameter bit [2:0][31:0] VEC1D = {32'd1, 32'd2, 32'd3}
//, parameter int NOVALUE_INT             Commented to avoid need to override.
//, parameter bit NOVALUE_BIT             Commented to avoid need to override.
  ) ();
endmodule

module CE4
  #(parameter integer FIVE = 5
  , parameter logic [2:0][31:0] VEC1D = {32'd1, 32'd2, 32'd3}
//, parameter integer NOVALUE_INTEGER     Commented to avoid need to override.
//, parameter logic NOVALUE_LOGIC         Commented to avoid need to override.
  ) ();
endmodule
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


  localparam IG_FIVE = 555;
  localparam IG_VEC1D = {32'd111, 32'd222, 32'd333};
  localparam IB_FIVE = "five";
  localparam IB_VEC1D = {11'd7, 22'd8, 33'd9};

  localparam int EG_FIVE = 555;
  localparam bit [2:0][31:0] EG_VEC1D = {32'd111, 32'd222, 32'd333};
  localparam bit [3:0] EB_FIVE = 4'bXZ01;
  localparam bit [2:0][9:0] EB_VEC1D = {10'd111, 10'd222, 10'd333};

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


  integer fd;
  initial begin
`ifdef QUESTA
    fd = $fopen("QUESTA.rpt");
`elsif XCELIUM
    fd = $fopen("XCELIUM.rpt");
`else
    fd = $fopen("OTHER.rpt");
`endif
    $fdisplay(fd, "$typename(s2)=%s $size(s2)=%0d", $typename(s2), $size(s2));
    $fdisplay(fd, "$typename(s4)=%s $size(s4)=%0d", $typename(s4), $size(s4));
    $fdisplay(fd, "$typename(sM)=%s $size(sM)=%0d", $typename(sM), $size(sM));
    // TODO: $display values of FOO_*, BAR_*, BAZ_*
    // TODO: $display types of (IG|IB|EG|EB)_(FIVE|VEC1D)
    // TODO: $display values of (IG|IB|EG|EB)_(FIVE|VEC1D)
    // TODO: $display types of child module parameters.
    // TODO: $display values of child module parameters.
    // TODO: $display value of `u_ce4_x.FIVE`.
    // TODO: Iterate through values of `a`, $display values of `b1`, `b2`.
    // TODO: $display values of WILDCARD_*.
    $fclose(fd);
    $finish();
  end

endmodule
