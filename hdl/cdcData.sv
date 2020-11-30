`include "dff.svh"

/** cdcData
 * 2-entry FIFO for Clock Domain Crossing data.
 * Bandwidth is 1 word for (nearly) every 2 cycles of the slowest clock.
 * For full bandwith (1 word for nearly every cycle of the slowest clock) full
 * Gray counters are required to be resynced as wptr,rptr.
 * If data source is bursty, then just putting single clock fifos on either
 * side gets equal burst bandwith (but not sustained).
 *
 * Based on Cummings minimal design, section 5.8.2 of
 * http://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf
*/
module cdcData #(
  parameter WIDTH = 8,  // Must be 1 or more.
  parameter FLOPS_NOT_MEM = 0
) (
  input  wire                         i_wclk,
  input  wire                         i_wrst,
  input  wire                         i_wcg,

  input  wire                         i_rclk,
  input  wire                         i_rrst,
  input  wire                         i_rcg,

  input  wire                         i_wpush,  // wput
  input  wire                         i_rpop,   // rget

  input  wire [WIDTH-1:0]             i_wdata,
  output wire [WIDTH-1:0]             o_rdata,

  output wire                         o_wfull,  // !wrdy
  output wire                         o_rempty  // !rrdy
);

wire doPush = !o_wfull && i_wpush;
wire doPop = !o_rempty && i_rpop;
wire wptrSynced;
wire rptrSynced;

`dff_cg_srst(reg, wptr, i_wclk, i_wcg, i_wrst, 1'b0)
`dff_cg_srst(reg, rptr, i_rclk, i_rcg, i_rrst, 1'b0)
always @* wptr_d = doPush ^ wptr_q;
always @* rptr_d = doPop ^ rptr_q;

generate if (FLOPS_NOT_MEM != 0) begin : useFlops

  (* mem2reg *) reg [WIDTH-1:0] entries_q [2]; // dff_cg_norst
  (* mem2reg *) reg [WIDTH-1:0] entries_d [2];

  always @* entries_d[0] = !wptr_q ? i_wdata : entries_q[0];
  always @* entries_d[1] = wptr_q ? i_wdata : entries_q[1];

  always @ (posedge i_wclk) if (i_wcg && doPush) begin
      entries_q[0] <= entries_d[0];
      entries_q[1] <= entries_d[1];
  end

  assign o_rdata = rptr_q ? entries_q[1] : entries_q[0];

end : useFlops else begin : useMem

  reg [WIDTH-1:0] entries_m [2];

  always @ (posedge i_wclk)
    if (i_wcg && doPush)
      entries_m[wptr_q] <= i_wdata;

  assign o_rdata = rptr_q ? entries_m[1] : entries_m[0];

end : useMem endgenerate

assign o_rempty = wptr_q & rptrSynced;
assign o_wfull = rptr_q & wptrSynced;

syncBit #(
  .DEBOUNCE_CYCLES (0),
  .EDGECNTR_W (1),
  .N_SYNC     (3)
) syncBit_wptr (
  .i_clk      (i_rclk),
  .i_cg       (i_rcg),
  .i_rst      (i_rrst),

  .i_bit      (wptr_q),

  .o_bit      (wptrSynced),
  .o_edge     (),
  .o_rise     (),
  .o_fall     (),
  .o_nEdge    (),
  .o_nRise    (),
  .o_nFall    ()
);
syncBit #(
  .DEBOUNCE_CYCLES (0),
  .EDGECNTR_W (1),
  .N_SYNC     (3)
) syncBit_rptr (
  .i_clk      (i_wclk),
  .i_cg       (i_wcg),
  .i_rst      (i_wrst),

  .i_bit      (rptr_q),

  .o_bit      (rptrSynced),
  .o_edge     (),
  .o_rise     (),
  .o_fall     (),
  .o_nEdge    (),
  .o_nRise    (),
  .o_nFall    ()
);

endmodule
