`include "dff.svh"
`include "misc.svh"

/** cdcFifo
 * N-entry FIFO for Clock Domain Crossing data, with higher bandwidth than
 * cdcData module.
 * Source and destination domains must be physically adjacent as a single block
 * of RAM or flops is used as a circular buffer.
*/
module cdcFifo #(
  parameter WIDTH = 8,  // >= 1.
  parameter DEPTH = 8,  // >= 2, must be power-of-2.
  parameter FLOPS_NOT_MEM = 0,

  // 0 -> gray-to-bin-inc-to-gray in single cycle.
  // 1 -> bin-inc and bin-to-gray separate FFs
  //      with result 1-cycle later.
  parameter FAST_NOT_SMALL = 0 // TODO
) (
  input  wire                         i_wclk,
  input  wire                         i_wrst,
  input  wire                         i_wcg,

  input  wire                         i_rclk,
  input  wire                         i_rrst,
  input  wire                         i_rcg,

  input  wire [WIDTH-1:0]             i_wdata,
  input  wire                         i_wvalid,  // wput
  output wire                         o_wready,  // wrdy

  output wire [WIDTH-1:0]             o_rdata,
  output wire                         o_rvalid,  // rrdy
  input  wire                         i_rready,  // rget

  output wire [$clog2(DEPTH)-1:0]     o_wptr,
  output wire [$clog2(DEPTH)-1:0]     o_rptr,

  output wire                         o_wpushed,
  output wire                         o_rpopped
);

genvar i;

localparam PTR_W = $clog2(DEPTH);

assign o_wpushed = o_wready && i_wvalid;
assign o_rpopped = o_rvalid && i_rready;

wire [PTR_W-1:0] wptrSynced;
wire [PTR_W-1:0] rptrSynced;
wire wptrWrap, wptrSyncedWrap, wptrSyncedPage;
wire rptrWrap, rptrSyncedWrap, rptrSyncedPage;

`dff_cg_srst(reg, wptrPage, i_wclk, i_wcg, i_wrst, 1'b0)
`dff_cg_srst(reg, rptrPage, i_rclk, i_rcg, i_rrst, 1'b0)
always @* wptrPage_d = wptrWrap ? !wptrPage_q : wptrPage_q;
always @* rptrPage_d = rptrWrap ? !rptrPage_q : rptrPage_q;

grayCounter #(
  .WIDTH          (PTR_W),
  .FAST_NOT_SMALL (FAST_NOT_SMALL)
) wptrGray (
  .i_clk  (i_wclk),
  .i_rst  (i_wrst),
  .i_cg   (i_wcg),
  .i_incr (o_wpushed),
  .o_wrap (wptrWrap),
  .o_gray (o_wptr)
);
grayCounter #(
  .WIDTH          (PTR_W),
  .FAST_NOT_SMALL (FAST_NOT_SMALL)
) rptrGray (
  .i_clk  (i_rclk),
  .i_rst  (i_rrst),
  .i_cg   (i_rcg),
  .i_incr (o_rpopped),
  .o_wrap (rptrWrap),
  .o_gray (o_rptr)
);

wire ptrsUnequalW = (o_wptr != rptrSynced) && !rptrSyncedWrap;
wire ptrsWrappedW = (rptrSyncedPage != wptrPage_q);
wire ptrsUnequalR = (wptrSynced != o_rptr) && !wptrSyncedWrap;
wire ptrsWrappedR = (wptrSyncedPage != rptrPage_q);

assign o_wready = ptrsUnequalW || !ptrsWrappedW; // !full
assign o_rvalid = ptrsUnequalR || ptrsWrappedR; // !empty

// TODO: FAST_NOT_SMALL requires line of flops on i_wdata and i_wvalid.
generate if (FLOPS_NOT_MEM != 0) begin : useFlops

  (* mem2reg *) reg [WIDTH-1:0] entries_q [DEPTH]; // dff_cg_norst
  (* mem2reg *) reg [WIDTH-1:0] entries_d [DEPTH];

  for (i = 0; i < DEPTH; i=i+1) begin : entries_b

    always @* entries_d[i] = (o_wpushed && (o_wptr == i)) ? i_wdata : entries_q[i];

    always @ (posedge i_wclk) if (i_wcg)
      entries_q[i] <= entries_d[i];

  end : entries_b

  assign o_rdata = entries_q[o_rptr];

end : useFlops else begin : useMem

  reg [WIDTH-1:0] entries_m [DEPTH];

  always @ (posedge i_wclk) if (i_wcg && o_wpushed)
    entries_m[o_wptr] <= i_wdata;

  assign o_rdata = entries_m[o_rptr];

end : useMem endgenerate

// Lower bits of gray counter pointers.
generate for (i = 0; i < (PTR_W-1); i=i+1) begin
  syncBit #(
    .DEBOUNCE_CYCLES  (0),
    .EDGECNTR_W       (1),
    .N_SYNC           (2)
  ) syncBit_wptr (
    .i_clk      (i_rclk),
    .i_cg       (i_rcg),
    .i_rst      (i_rrst),

    .i_bit      (o_wptr[i]),

    .o_bit      (wptrSynced[i]),
    .o_edge     (),
    .o_rise     (),
    .o_fall     (),
    .o_nEdge    (),
    .o_nRise    (),
    .o_nFall    ()
  );
  syncBit #(
    .DEBOUNCE_CYCLES  (0),
    .EDGECNTR_W       (1),
    .N_SYNC           (2)
  ) syncBit_rptr (
    .i_clk      (i_wclk),
    .i_cg       (i_wcg),
    .i_rst      (i_wrst),

    .i_bit      (o_rptr[i]),

    .o_bit      (rptrSynced[i]),
    .o_edge     (),
    .o_rise     (),
    .o_fall     (),
    .o_nEdge    (),
    .o_nRise    (),
    .o_nFall    ()
  );
end endgenerate

// Upper bit syncs have extra flop toggling on fall.
syncBit #(
  .DEBOUNCE_CYCLES  (0),
  .EDGECNTR_W       (1),
  .N_SYNC           (2)
) syncBit_wptrMsb (
  .i_clk      (i_rclk),
  .i_cg       (i_rcg),
  .i_rst      (i_rrst),

  .i_bit      (o_wptr[PTR_W-1]),

  .o_bit      (wptrSynced[PTR_W-1]),
  .o_edge     (wptrSyncedWrap),
  .o_rise     (),
  .o_fall     (),
  .o_nEdge    (),
  .o_nRise    (),
  .o_nFall    (wptrSyncedPage)
);
syncBit #(
  .DEBOUNCE_CYCLES  (0),
  .EDGECNTR_W       (1),
  .N_SYNC           (2)
) syncBit_rptrMsb (
  .i_clk      (i_wclk),
  .i_cg       (i_wcg),
  .i_rst      (i_wrst),

  .i_bit      (o_rptr[PTR_W-1]),

  .o_bit      (rptrSynced[PTR_W-1]),
  .o_edge     (rptrSyncedWrap),
  .o_rise     (),
  .o_fall     (),
  .o_nEdge    (),
  .o_nRise    (),
  .o_nFall    (rptrSyncedPage)
);

endmodule
