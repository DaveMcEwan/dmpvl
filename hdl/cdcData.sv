`include "dff.svh"

/** cdcData
 * 2-entry FIFO for Clock Domain Crossing data.
 * If data source is bursty, then just putting single clock fifos on either
 * side gets equal burst bandwith (but not sustained).
 *
 * Linear should be used when sender and receiver are spacially distant, and
 * lower bandwidth is acceptable.
 * Circular requires sender and receiver to be spacially close to the same RAM
 * or flops used for entries, but removes a clock cycle on both sides.
 *
 * LINEAR based on Cummings MCP formulation with ack feedback, section 5.6.3 of
 * http://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf
 * Should synthesize to MCP formulation with feedback, section 5.6.2, when
 * o_rvalid is unconnected and i_rready is tied high.
 *
 * CIRCULAR based on Cummings design, section 5.8.2 of
 * http://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf
 * Bandwidth is 1 word for (nearly) every 2 cycles of the slowest clock.
 * For full bandwith (1 word for nearly every cycle of the slowest clock) full
 * Gray counters are required to be resynced as wptr,rptr.
*/
module cdcData #(
  parameter WIDTH = 8,  // >= 1.
  parameter TOPOLOGY = 0,  // 0->CIRCULAR, 1->LINEAR.
  parameter FLOPS_NOT_MEM = 0 // Only used in CIRCULAR, not used in LINEAR.
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
  input  wire                         i_rready   // rget
);

wire doWrite = o_wready && i_wvalid;
wire doRead = o_rvalid && i_rready;

generate if (TOPOLOGY != 0) begin : topoLinear
  // Write and read domains separated with named blocks.
  // "if (1)" workaround for iverilog bug

  wire [WIDTH-1:0] wData;
  wire wEnCtrl;
  wire rAckCtrl;

  if (1) begin : wDomain
    wire wAckEdge;
    `dff_cg_srst(reg [WIDTH-1:0], wData, i_wclk, i_wcg, i_wrst, '0)
    `dff_cg_srst(reg, wEnCtrl, i_wclk, i_wcg, i_wrst, 1'b0)
    `dff_cg_srst(reg, wFsm, i_wclk, i_wcg, i_wrst, 1'b0)
    assign wData = wData_q;
    assign wEnCtrl = wEnCtrl_q;
    assign o_wready = !wFsm_q;

    always @* wData_d = doWrite ? i_wdata : wData_q;
    always @* wEnCtrl_d = wEnCtrl_q ^ doWrite;
    always @*
      if (doWrite)                 wFsm_d = 1'b1;
      else if (wFsm_q && wAckEdge) wFsm_d = 1'b0;
      else                         wFsm_d = wFsm_q;

    syncBit #(
      .DEBOUNCE_CYCLES  (0),
      .EDGECNTR_W       (1),
      .N_SYNC           (2)
    ) syncBit_ackCtrl (
      .i_clk      (i_rclk),
      .i_cg       (i_rcg),
      .i_rst      (i_rrst),

      .i_bit      (rAckCtrl),

      .o_bit      (),
      .o_edge     (wAckEdge),
      .o_rise     (),
      .o_fall     (),
      .o_nEdge    (),
      .o_nRise    (),
      .o_nFall    ()
    );
  end : wDomain

  if (1) begin : rDomain
    wire rEnEdge;
    `dff_cg_srst(reg [WIDTH-1:0], rData, i_rclk, i_rcg, i_rrst, '0)
    `dff_cg_srst(reg, rAckCtrl, i_rclk, i_rcg, i_rrst, 1'b0)
    `dff_cg_srst(reg, rFsm, i_rclk, i_rcg, i_rrst, 1'b0)
    assign o_rdata = rData_q;
    assign rAckCtrl = rAckCtrl_q;
    assign o_rvalid = rFsm_q;

    wire rAcceptData = !rFsm_q && rEnEdge;
    always @* rData_d = rAcceptData ? wData : rData_q;
    always @* rAckCtrl_d = rAckCtrl_q ^ doRead;
    always @*
      if (rAcceptData)  rFsm_d = 1'b1;
      else if (doRead)  rFsm_d = 1'b0;
      else              rFsm_d = rFsm_q;

    syncBit #(
      .DEBOUNCE_CYCLES  (0),
      .EDGECNTR_W       (1),
      .N_SYNC           (2)
    ) syncBit_enCtrl (
      .i_clk      (i_rclk),
      .i_cg       (i_rcg),
      .i_rst      (i_rrst),

      .i_bit      (wEnCtrl),

      .o_bit      (),
      .o_edge     (rEnEdge),
      .o_rise     (),
      .o_fall     (),
      .o_nEdge    (),
      .o_nRise    (),
      .o_nFall    ()
    );
  end : rDomain

end : topoLinear else begin : topoCircular

  `dff_cg_srst(reg, wptr, i_wclk, i_wcg, i_wrst, 1'b0)
  `dff_cg_srst(reg, rptr, i_rclk, i_rcg, i_rrst, 1'b0)
  always @* wptr_d = doWrite ^ wptr_q;
  always @* rptr_d = doRead ^ rptr_q;

  if (FLOPS_NOT_MEM != 0) begin : useFlops

    (* mem2reg *) reg [WIDTH-1:0] entries_q [2]; // dff_cg_norst
    (* mem2reg *) reg [WIDTH-1:0] entries_d [2];

    always @* entries_d[0] = !wptr_q ? i_wdata : entries_q[0];
    always @* entries_d[1] = wptr_q ? i_wdata : entries_q[1];

    always @ (posedge i_wclk) if (i_wcg && doWrite) begin
      entries_q[0] <= entries_d[0];
      entries_q[1] <= entries_d[1];
    end

    assign o_rdata = rptr_q ? entries_q[1] : entries_q[0];

  end : useFlops else begin : useMem

    reg [WIDTH-1:0] entries_m [2];

    always @ (posedge i_wclk) if (i_wcg && doWrite)
      entries_m[wptr_q] <= i_wdata;

    assign o_rdata = entries_m[rptr_q];

  end : useMem

  wire wptrSynced;
  wire rptrSynced;
  assign o_wready = !(wptr_q ^ rptrSynced);
  assign o_rvalid = rptr_q ^ wptrSynced;

  syncBit #(
    .DEBOUNCE_CYCLES  (0),
    .EDGECNTR_W       (1),
    .N_SYNC           (2)
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
    .DEBOUNCE_CYCLES  (0),
    .EDGECNTR_W       (1),
    .N_SYNC           (2)
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

end : topoCircular endgenerate

endmodule
