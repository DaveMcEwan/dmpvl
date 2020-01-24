`ifndef DFF_VH_
`define DFF_VH_

/** Flop macros
 * These are to make the intent of flop inferences easy to determine.
 * Naming convention:
 *  - dff   Infers a collection of D-type flip flops.
 *  - dlatch Infers a collection of D-type latches.
 *  - cg    Infers a clockgate, often a good idea for power.
 *  - nocg  Does not infer a clockgate.
 *  - arst  Infers asynchronous active-high reset.
 *  - arstn Infers asynchronous active-low reset.
 *  - srst  Infers synchronous active-high reset.
 *  - srstn Infers synchronous active-low reset.
 *  - norst Infers no reset, often a good idea for area.
 *  - upk   Functionally equivalent macros for unpacked vectors.
 *  - d     Predefined input to flop, cuts down on boilerplate.
 *  - flag  Single bit control flag, cuts down on boilerplate.
 *
 * Recommendations:
 *  - Use clockgates where possible.
 *    - If the synth tool decides it isn't worth it for power then it can
 *      implement the clockgate as a recirculating mux, but it should have the
 *      choice, particularly if the number of flops is parameterized.
 *  - Prefer non-reset (norst).
 *    - Non-reset flops are smaller on ASIC designs.
 *    - Reset network will be smaller, so less like an antenna.
 *    - Especially useful for datapath where reset value is meaningless.
 *  - Prefer active-high resets (rst) instead of active-low (rstn).
 *    - On FPGA targets additional LUTs may be used as inverters to support
 *      active-low behaviour.
 *    - Consistency is more important though.
 *  - Prefer synchronous resets (srst) instead of asynchronous (arst).
 *    - This prevents huge global async resets acting as antennas with lots of
 *      unintended consequences on large designs.
 *  - Use unpacked arrays where elements don't need to grouped together.
 *    - Keeps code small and tidy.
 *    - Lets synth tools ungroup logic.
 *    - For FPGA synthesis targets this may or may not be a good thing so
 *      requires expeimentation on a case-by-case basis.
 *
 * TL;DR:
 *  - dff_cg_norst[_upk]     Datapath
 *  - dff_[no]cg_srst[_upk]  Control path
 */

// {{{ `dff_cg_arst (logic [9:0], foo, i_clk, i_cg, i_rst, '0)
`define dff_cg_arst(t, n, clk, cg, rst, rstval) \
t n``_d, n``_q; \
always @ (posedge clk or posedge rst) \
  if (rst)     n``_q <= rstval; \
  else if (cg) n``_q <= n``_d; \
  else         n``_q <= n``_q;
// }}}
// {{{ `dff_cg_arstn (logic [9:0], foo, i_clk, i_cg, i_rstn, '0)
`define dff_cg_arstn(t, n, clk, cg, rstn, rstval) \
t n``_d, n``_q; \
always @ (posedge clk or negedge rstn) \
  if (!rstn)   n``_q <= rstval; \
  else if (cg) n``_q <= n``_d; \
  else         n``_q <= n``_q;
// }}}
// {{{ `dff_nocg_arst (logic [9:0], foo, i_clk, i_rst, '0)
`define dff_nocg_arst(t, n, clk, rst, rstval) \
t n``_d, n``_q; \
always @ (posedge clk or posedge rst) \
  if (rst) n``_q <= rstval; \
  else     n``_q <= n``_d;
// }}}
// {{{ `dff_nocg_arstn (logic [9:0], foo, i_clk, i_rstn, '0)
`define dff_nocg_arstn(t, n, clk, rstn, rstval) \
t n``_d, n``_q; \
always @ (posedge clk or negedge rstn) \
  if (!rstn) n``_q <= rstval; \
  else       n``_q <= n``_d;
// }}}
// {{{ `dff_cg_srst (logic [9:0], foo, i_clk, i_cg, i_rst, '0)
`define dff_cg_srst(t, n, clk, cg, rst, rstval) \
t n``_d, n``_q; \
always @ (posedge clk) \
  if (rst)     n``_q <= rstval; \
  else if (cg) n``_q <= n``_d; \
  else         n``_q <= n``_q;
// }}}
// {{{ `dff_cg_srstn (logic [9:0], foo, i_clk, i_cg, i_rstn, '0)
`define dff_cg_srstn(t, n, clk, cg, rstn, rstval) \
t n``_d, n``_q; \
always @ (posedge clk) \
  if (!rstn)   n``_q <= rstval; \
  else if (cg) n``_q <= n``_d; \
  else         n``_q <= n``_q;
// }}}
// {{{ `dff_cg_srst_d (logic [9:0], foo, i_clk, i_cg, i_rst, '0, predefined_d)
`define dff_cg_srst_d(t, n, clk, cg, rst, rstval, d) \
t n``_q; \
always @ (posedge clk) \
  if (rst)     n``_q <= rstval; \
  else if (cg) n``_q <= d; \
  else         n``_q <= n``_q;
// }}}
// {{{ `dff_nocg_srst_d (logic [9:0], foo, i_clk, i_rst, '0, predefined_d)
`define dff_nocg_srst_d(t, n, clk, rst, rstval, d) \
t n``_q; \
always @ (posedge clk) \
  if (rst) n``_q <= rstval; \
  else     n``_q <= d;
// }}}
// {{{ `dff_nocg_srst (logic [9:0], foo, i_clk, i_rst, '0)
`define dff_nocg_srst(t, n, clk, rst, rstval) \
t n``_d, n``_q; \
always @ (posedge clk) \
  if (rst) n``_q <= rstval; \
  else     n``_q <= n``_d;
// }}}
// {{{ `dff_nocg_srstn (logic [9:0], foo, i_clk, i_rstn, '0)
`define dff_nocg_srstn(t, n, clk, rstn, rstval) \
t n``_d, n``_q; \
always @ (posedge clk) \
  if (!rstn) n``_q <= rstval; \
  else       n``_q <= n``_d;
// }}}
// {{{ `dff_cg_norst (logic [9:0], foo, i_clk, i_cg)
`define dff_cg_norst(t, n, clk, cg) \
t n``_d, n``_q; \
always @ (posedge clk) \
  if (cg) n``_q <= n``_d; \
  else    n``_q <= n``_q;
// }}}
// {{{ `dff_nocg_norst (logic [9:0], foo, i_clk)
`define dff_nocg_norst(t, n, clk) \
t n``_d, n``_q; \
always @ (posedge clk) \
  n``_q <= n``_d;
// }}}
// {{{ `dff_cg_norst_d (logic [9:0], foo, i_clk, i_cg, predefined_d)
`define dff_cg_norst_d(t, n, clk, cg, d) \
t n``_q; \
always @ (posedge clk) \
  if (cg) n``_q <= d; \
  else    n``_q <= n``_q;
// }}}
// {{{ `dff_nocg_norst_d (logic [9:0], foo, i_clk, predefined_d)
`define dff_nocg_norst_d(t, n, clk, d) \
t n``_q; \
always @ (posedge clk) \
  n``_q <= d;
// }}}
// {{{ `dlatch (logic [9:0], foo, enable)
`define dlatch(t, n, en) \
t n``_ld, n``_lq; \
always @* if (en) \
  n``_lq <= n``_ld;
// }}}

// Now the same macros but including parameter for unpacked vectors.
// NOTE: yosys doesn't support the wholesale assignment of unpacked arrays here.

// {{{ `dff_cg_arst_upk (logic [9:0], foo, [3][4], i_clk, i_cg, i_rst, '0)
`define dff_cg_arst_upk(t, n, u, clk, cg, rst, rstval) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk or posedge rst) \
  if (rst)     n``_q <= rstval; \
  else if (cg) n``_q <= n``_d; \
  else         n``_q <= n``_q;
// }}}
// {{{ `dff_cg_arstn_upk (logic [9:0], foo, [3][4], i_clk, i_cg, i_rstn, '0)
`define dff_cg_arstn_upk(t, n, u, clk, cg, rstn, rstval) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk or negedge rstn) \
  if (!rstn)   n``_q <= rstval; \
  else if (cg) n``_q <= n``_d; \
  else         n``_q <= n``_q;
// }}}
// {{{ `dff_nocg_arst_upk (logic [9:0], foo, [3][4], i_clk, i_rst, '0)
`define dff_nocg_arst_upk(t, n, u, clk, rst, rstval) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk or posedge rst) \
  if (rst) n``_q <= rstval; \
  else     n``_q <= n``_d;
// }}}
// {{{ `dff_nocg_arstn_upk (logic [9:0], foo, [3][4], i_clk, i_rstn, '0)
`define dff_nocg_arstn_upk(t, n, u, clk, rstn, rstval) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk or negedge rstn) \
  if (!rstn) n``_q <= rstval; \
  else       n``_q <= n``_d;
// }}}
// {{{ `dff_cg_srst_upk (logic [9:0], foo, [3][4], i_clk, i_cg, i_rst, '0)
`define dff_cg_srst_upk(t, n, u, clk, cg, rst, rstval) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk) \
  if (rst)     n``_q <= rstval; \
  else if (cg) n``_q <= n``_d; \
  else         n``_q <= n``_q;
// }}}
// {{{ `dff_cg_srstn_upk (logic [9:0], foo, [3][4], i_clk, i_cg, i_rstn, '0)
`define dff_cg_srstn_upk(t, n, u, clk, cg, rstn, rstval) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk) \
  if (!rstn)   n``_q <= rstval; \
  else if (cg) n``_q <= n``_d; \
  else         n``_q <= n``_q;
// }}}
// {{{ `dff_nocg_srst_upk (logic [9:0], foo, [3][4], i_clk, i_rst, '0)
`define dff_nocg_srst_upk(t, n, u, clk, rst, rstval) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk) \
  if (rst) n``_q <= rstval; \
  else     n``_q <= n``_d;
// }}}
// {{{ `dff_nocg_srstn_upk (logic [9:0], foo, [3][4], i_clk, i_rstn, '0)
`define dff_nocg_srstn_upk(t, n, u, clk, rstn, rstval) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk) \
  if (!rstn) n``_q <= rstval; \
  else       n``_q <= n``_d;
// }}}
// {{{ `dff_cg_norst_upk (logic [9:0], foo, [3][4], i_clk, i_cg)
`define dff_cg_norst_upk(t, n, u, clk, cg) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk) \
  if (cg) n``_q <= n``_d; \
  else    n``_q <= n``_q;
// }}}
// {{{ `dff_nocg_norst_upk (logic [9:0], foo, [3][4], i_clk)
`define dff_nocg_norst_upk(t, n, u, clk) \
t n``_d u; \
t n``_q u; \
always @ (posedge clk) \
  n``_q <= n``_d;
// }}}
// {{{ `dlatch_upk (logic [9:0], foo, [3][4], enable)
`define dlatch_upk(t, n, u, en) \
t n``_ld u; \
t n``_lq u; \
always @* if (en) \
  n``_lq <= n``_ld;
// }}}

// Only one macro is defined for flag register as anything else really needs
// close attention, which a macro would distract from.
// Synchronous reset to zero.
// {{{ `dff_flag (foo, i_clk, i_rst, fooRaise, fooLower)
`define dff_flag(n, clk, rst, raise, lower) \
reg n``_d, n``_q; \
wire n``_goUp = raise && !lower; \
wire n``_goDn = lower && !raise; \
always @ (posedge clk) \
  if (rst || (n``_goDn))  n``_q <= 1'b0; \
  else if (n``_goUp)      n``_q <= 1'b1; \
  else                    n``_q <= n``_q;
// }}}

`endif // DFF_VH_
