`include "dff.svh"

/** syncBit
 * Synchronize single bit to this clock domain.
 * Optional debouncing for highly metastable inputs, such as pushbutton.
 *
 * N_SYNC defines the number of resync flops (before debouncing), and should
 * generally be at least 2
 * Diagram of non-debounce circuit:
 *
 *               Large        Regular         Regular
 *               sync[0]      sync[1]         sync[2]
 *               sync[0]      sync[N_SYNC-1]  sync[N_SYNC]
 *
 *               +---+        +---+           +---+
 *    i_bit ---> |   | ---->  |   | ----o---> |   | --+
 *               +-^-+        +-^-+     |     +-^-+   |
 *                                      |             |
 *                                      +------------XOR ---> o_edge
 *                                      |
 *                                      |
 *                                      +-------------------> o_bit/stableBit
 *
 * Physically large flop identified with regex something like:
 *    *.syncBit*.sync_q[0]
 * This should drive no logic, only sync[1] flop.
 *
 * o_bit: Current state of synced+debounced bit.
 *    Driven by flop.
 * o_edge: Pulse for single cycle when synced+debounced bit changes value.
 *    Driven by logic.
 *    If unconnected and DEBOUNCE_CYCLES=0 then sync_q[N_SYNC] may be removed
 *    by synthesis.
 * o_nEdge, o_nRise, o_nFall: Upcounters incrementing on edge, posedge, negedge.
 *    Driven by flops.
 *    Setting EDGECNTR_W high, say 32, may be useful for simulation/debugging
 *    even if only 1 or 0 output bits are actually connected.
 *    Bit0 of o_nRise may be used as a toggle-on-press for pushbutton, and bit0
 *    of o_nFall may be similarly used as a toggle-on-release.
 *    Unconnected bits should be removed by synthesis.
 *    Where DEBOUNCE_CYCLES!=0, bit0 of o_nEdge is equivalent to o_bit so should
 *    not be connected to allow synthesis to remove it.
*/
module syncBit #(
  parameter DEBOUNCE_CYCLES = 0,  // 0 to disable debouncing, or >= 2.
  parameter EDGECNTR_W = 1,       // >= 1.
  parameter N_SYNC = 2            // >=2
) (
  input  wire                         i_clk,
  input  wire                         i_rst,
  input  wire                         i_cg,

  input  wire                         i_bit, // From other clock domain

  output wire                         o_bit,
  output wire                         o_edge,
  output wire                         o_rise,
  output wire                         o_fall,

  output wire [EDGECNTR_W-1:0]        o_nEdge,
  output wire [EDGECNTR_W-1:0]        o_nRise,
  output wire [EDGECNTR_W-1:0]        o_nFall
);

// Higher order bits should be physically larger flops, if possible, to reduce
// MTBF of metastability propagation by having shorter sample windows.
`dff_cg_srst(reg [N_SYNC:0], sync, i_clk, i_cg, i_rst, '0)
always @* sync_d = {sync_q[N_SYNC-1:0], i_bit};

wire stableBit = sync_q[N_SYNC-1];
wire changed = (sync_q[N_SYNC] != stableBit);

generate if (DEBOUNCE_CYCLES == 0) begin
  assign o_bit = stableBit;
  assign o_edge = changed;
end else begin
  `dff_cg_srst(reg [$clog2(DEBOUNCE_CYCLES+1)-1:0], cntr, i_clk, i_cg, i_rst, '0)
  `dff_cg_srst(reg, debounced, i_clk, i_cg, i_rst, 1'b0)

  wire inputToggle = stableBit != debounced_q;

  always @*
    if (changed)          cntr_d = 'd0;
    else if (inputToggle) cntr_d = cntr_q + 'd1;
    else                  cntr_d = cntr_q;

  always @* debounced_d = o_edge ? stableBit : debounced_q;

  assign o_bit = debounced_q;
  assign o_edge = (cntr_q == DEBOUNCE_CYCLES) && inputToggle;
end endgenerate

assign o_rise = o_edge && stableBit;
assign o_fall = o_edge && !stableBit;
`dff_upcounter(reg [EDGECNTR_W-1:0], nEdge, i_clk, i_cg && o_edge, i_rst)
`dff_upcounter(reg [EDGECNTR_W-1:0], nRise, i_clk, i_cg && o_rise, i_rst)
`dff_upcounter(reg [EDGECNTR_W-1:0], nFall, i_clk, i_cg && o_fall, i_rst)
assign o_nEdge = nEdge_q;
assign o_nRise = nRise_q;
assign o_nFall = nFall_q;

endmodule
