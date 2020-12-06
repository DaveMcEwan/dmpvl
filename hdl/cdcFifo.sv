`include "asrt.svh"
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

  // 0 -> gray-->bin-->incr-->gray in single cycle.
  // 1 -> bin-->incl, bin-->gray separate FFs with result 1-cycle later.
  parameter TOPOLOGY = 0 // TODO
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

wire [WIDTH-1:0] wdata, rdata;
wire [PTR_W:0] wptrBin, rptrBin;
wire [PTR_W:0] wptrSyncedGray, rptrSyncedGray;
wire [PTR_W:0] wptrSyncedBin, rptrSyncedBin;
`dff_cg_srst(reg [PTR_W:0], wptrGray, i_wclk, i_wcg, i_wrst, '0)
`dff_cg_srst(reg [PTR_W:0], rptrGray, i_rclk, i_rcg, i_rrst, '0)

// TODO: Separate TOPOLOGY for write and read sides.
generate if (TOPOLOGY) begin
  `dff_cg_srst(reg, wpushed, i_wclk, i_wcg, i_wrst, 1'b0)
  `dff_cg_srst(reg, rpopped, i_rclk, i_rcg, i_rrst, 1'b0)
  always @* wpushed_d = o_wready && i_wvalid;
  always @* rpopped_d = o_rvalid && i_rready;
  assign o_wpushed = wpushed_q;
  assign o_rpopped = rpopped_q;

  `dff_cg_srst(reg [PTR_W:0], wptrBin, i_wclk, i_wcg && o_wpushed, i_wrst, '0)
  `dff_cg_srst(reg [PTR_W:0], rptrBin, i_rclk, i_rcg && o_rpopped, i_rrst, '0)
  always @* wptrBin_d = wptrBin_q + 'd1;
  always @* rptrBin_d = rptrBin_q + 'd1;
  assign wptrBin = wptrBin_q;
  assign rptrBin = rptrBin_q;

  `dff_cg_srst(reg [PTR_W-1:0], wptr, i_wclk, i_wcg, i_wrst, '0)
  `dff_cg_srst(reg [PTR_W-1:0], rptr, i_rclk, i_rcg, i_rrst, '0)
  always @* wptr_d = wptrBin_q`LSb(PTR_W);
  always @* rptr_d = rptrBin_q`LSb(PTR_W);
  assign o_wptr = wptr_q;
  assign o_rptr = rptr_q;

  binToGray #(.WIDTH(PTR_W+1)) u_b2gWptr (.i_bin(wptrBin_q), .o_gray(wptrGray_d));
  binToGray #(.WIDTH(PTR_W+1)) u_b2gRptr (.i_bin(rptrBin_q), .o_gray(rptrGray_d));

  `dff_cg_srst(reg [PTR_W:0], wptrSyncedBin, i_wclk, i_wcg, i_wrst, '0)
  `dff_cg_srst(reg [PTR_W:0], rptrSyncedBin, i_rclk, i_rcg, i_rrst, '0)
  grayToBin #(.WIDTH(PTR_W+1)) u_g2bWsynced (.i_gray(wptrSyncedGray), .o_bin(wptrSyncedBin_d));
  grayToBin #(.WIDTH(PTR_W+1)) u_g2bRsynced (.i_gray(rptrSyncedGray), .o_bin(rptrSyncedBin_d));
  assign wptrSyncedBin = wptrSyncedBin_q;
  assign rptrSyncedBin = rptrSyncedBin_q;

  `dff_cg_norst(reg [WIDTH-1:0], wdata, i_wclk, i_wcg)
  `dff_cg_norst(reg [WIDTH-1:0], rdata, i_rclk, i_rcg)
  always @* wdata_d = wpushed_d ? i_wdata : wdata_q;
  always @* rdata_d = rpopped_d ? rdata : rdata_q;
  assign wdata = wdata_q;
  assign o_rdata = rdata_q;
end else begin
  assign o_wpushed = o_wready && i_wvalid;
  assign o_rpopped = o_rvalid && i_rready;

  wire [PTR_W:0] b2gWptr, b2gRptr;
  binToGray #(.WIDTH(PTR_W+1)) u_b2gWptr (.i_bin(wptrBin + 'd1), .o_gray(b2gWptr));
  binToGray #(.WIDTH(PTR_W+1)) u_b2gRptr (.i_bin(rptrBin + 'd1), .o_gray(b2gRptr));
  always @* wptrGray_d = o_wpushed ? b2gWptr : wptrGray_q;
  always @* rptrGray_d = o_rpopped ? b2gRptr : rptrGray_q;

  grayToBin #(.WIDTH(PTR_W+1)) u_g2bWptr (.i_gray(wptrGray_q), .o_bin(wptrBin));
  grayToBin #(.WIDTH(PTR_W+1)) u_g2bRptr (.i_gray(rptrGray_q), .o_bin(rptrBin));

  assign o_wptr = wptrBin`LSb(PTR_W);
  assign o_rptr = rptrBin`LSb(PTR_W);

  grayToBin #(.WIDTH(PTR_W+1)) u_g2bWsynced (.i_gray(wptrSyncedGray), .o_bin(wptrSyncedBin));
  grayToBin #(.WIDTH(PTR_W+1)) u_g2bRsynced (.i_gray(rptrSyncedGray), .o_bin(rptrSyncedBin));

  assign wdata = i_wdata;
  assign o_rdata = rdata;
end endgenerate

wire ptrsUnequalW = (wptrBin`LSb(PTR_W) != rptrSyncedBin`LSb(PTR_W));
wire ptrsUnequalR = (rptrBin`LSb(PTR_W) != wptrSyncedBin`LSb(PTR_W));
wire ptrsWrappedW = (wptrBin[PTR_W] != rptrSyncedBin[PTR_W]);
wire ptrsWrappedR = (rptrBin[PTR_W] != wptrSyncedBin[PTR_W]);

assign o_wready = ptrsUnequalW || !ptrsWrappedW; // !full
assign o_rvalid = ptrsUnequalR || ptrsWrappedR; // !empty

generate if (FLOPS_NOT_MEM != 0) begin : useFlops

  (* mem2reg *) reg [WIDTH-1:0] entries_q [DEPTH]; // dff_cg_norst
  (* mem2reg *) reg [WIDTH-1:0] entries_d [DEPTH];

  for (i = 0; i < DEPTH; i=i+1) begin : entries_b

    always @* entries_d[i] = (o_wpushed && (o_wptr == i)) ? wdata : entries_q[i];

    always @ (posedge i_wclk) if (i_wcg)
      entries_q[i] <= entries_d[i];

  end : entries_b

  assign rdata = entries_q[o_rptr];

end : useFlops else begin : useMem

  reg [WIDTH-1:0] entries_m [DEPTH];

  always @ (posedge i_wclk) if (i_wcg && o_wpushed)
    entries_m[o_wptr] <= wdata;

  assign rdata = entries_m[o_rptr];

end : useMem endgenerate

generate for (i = 0; i <= PTR_W; i=i+1) begin
  syncBit #(
    .DEBOUNCE_CYCLES  (0),
    .EDGECNTR_W       (1),
    .N_SYNC           (2)
  ) syncBit_wptr (
    .i_clk      (i_rclk),
    .i_cg       (i_rcg),
    .i_rst      (i_rrst),

    .i_bit      (wptrGray_q[i]),

    .o_bit      (wptrSyncedGray[i]),
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

    .i_bit      (rptrGray_q[i]),

    .o_bit      (rptrSyncedGray[i]),
    .o_edge     (),
    .o_rise     (),
    .o_fall     (),
    .o_nEdge    (),
    .o_nRise    (),
    .o_nFall    ()
  );
end endgenerate

`ifndef SYNTHESIS
`dff_upcounter(reg [31:0], nPushed, i_wclk, i_wcg && o_wpushed, i_wrst)
`dff_upcounter(reg [31:0], nPopped, i_rclk, i_rcg && o_rpopped, i_rrst)
wire [31:0] nDiff = nPushed_q - nPopped_q;
wire tooManyPush = nDiff > DEPTH;
wire tooManyPop = nPopped_q > nPushed_q;
`asrtw_en (!tooManyPush, i_wclk, i_wcg)
`asrtw_en (!tooManyPop, i_rclk, i_rcg)
`endif

endmodule
