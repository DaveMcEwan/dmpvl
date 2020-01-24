`ifndef ASRT_VH_
`define ASRT_VH_

`ifdef SYNTHESIS
  // Assertion macros defined as nothing in synthesis.
  // NOTE: Not the same as FORMAL, which has not been attempted yet.

  `define asrt(nm, trigger, en, cond)
  `define asrtw(wirenm, trigger)
  `define asrtw_en(wirenm, trigger, en)
`else

/** Assertion macros
 * These are to make writing regular assertions easily.
 * Use the plain asrt if you're unsure.
 * asrtw,asrtw_en are provided as convenience for when asrt is difficult.
 */

// {{{ `asrt (foo, i_clk, fooEnable, exprShouldBeTrue)
// Creates a wire "a_foo" which can be trivially assumed.
`define asrt(nm, trigger, en, cond) \
wire a_``nm = !(en) || (cond); \
always @ (posedge (trigger)) \
  assert (a_``nm) \
  else $display("ERROR:t%0t:%m:%0d: a_``nm", $time, `__LINE__);
// }}} asrt

// {{{ `asrtw (foo, i_clk)
// Use with a predefined wire assigned to be usually 1, so assertion fires iff
// wire value is not 1 when trigger condition occurs.
// Can trivially be made into an assumption.
`define asrtw(wirenm, trigger) \
always @ (posedge (trigger)) \
  assert (wirenm) \
  else $display("ERROR:t%0t:%m:%0d: wirenm", $time, `__LINE__);
// }}} asrtw

// {{{ `asrtw_en (foo, i_clk, fooEnable)
// Use with a predefined wire assigned to be usually 1, so assertion fires iff
// wire value is not 1 when trigger condition occurs and enable is true.
// NOTE: Not trivial to turn into assumption.
`define asrtw_en(wirenm, trigger, en) \
always @ (posedge (trigger)) \
  if (en) assert (wirenm) \
  else $display("ERROR:t%0t:%m:%0d: wirenm", $time, `__LINE__);
// }}} asrtw_en

`endif

`endif // ASRT_VH_
