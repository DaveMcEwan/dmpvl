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

assign o_wpushed = o_wready && i_wvalid;
assign o_rpopped = o_rvalid && i_rready;

wire [PTR_W:0] wptrBin, rptrBin;
`dff_cg_srst(reg [PTR_W:0], wptrGray, i_wclk, i_wcg && o_wpushed, i_wrst, '0)
`dff_cg_srst(reg [PTR_W:0], rptrGray, i_rclk, i_rcg && o_rpopped, i_rrst, '0)
binToGray #(.WIDTH(PTR_W+1)) u_b2gWptr (.i_bin(wptrBin + 'd1), .o_gray(wptrGray_d));
binToGray #(.WIDTH(PTR_W+1)) u_b2gRptr (.i_bin(rptrBin + 'd1), .o_gray(rptrGray_d));
grayToBin #(.WIDTH(PTR_W+1)) u_g2bWptr (.i_gray(wptrGray_q), .o_bin(wptrBin));
grayToBin #(.WIDTH(PTR_W+1)) u_g2bRptr (.i_gray(rptrGray_q), .o_bin(rptrBin));

assign o_wptr = wptrBin`LSb(PTR_W);
assign o_rptr = rptrBin`LSb(PTR_W);

wire [PTR_W:0] wptrSyncedGray, rptrSyncedGray;
wire [PTR_W:0] wptrSyncedBin, rptrSyncedBin;
grayToBin #(.WIDTH(PTR_W+1)) u_g2bWsynced (.i_gray(wptrSyncedGray), .o_bin(wptrSyncedBin));
grayToBin #(.WIDTH(PTR_W+1)) u_g2bRsynced (.i_gray(rptrSyncedGray), .o_bin(rptrSyncedBin));

wire ptrsUnequalW = (o_wptr != rptrSyncedBin`LSb(PTR_W));
wire ptrsUnequalR = (o_rptr != wptrSyncedBin`LSb(PTR_W));
wire ptrsWrappedW = (wptrGray_q[PTR_W] != rptrSyncedGray[PTR_W]);
wire ptrsWrappedR = (rptrGray_q[PTR_W] != wptrSyncedGray[PTR_W]);

assign o_wready = ptrsUnequalW || !ptrsWrappedW; // !full
assign o_rvalid = ptrsUnequalR || ptrsWrappedR; // !empty

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
