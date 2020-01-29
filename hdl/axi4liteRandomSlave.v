`include "dff.vh"

module axi4liteRandomSlave #(
  parameter IDLE_TIMEOUT = 3,
  parameter PROB_W = 8,
  parameter N_MEM_WORD = 5, // Small for synthesis, maybe 4k for simulation.
  parameter ADDR_BASE = 32'hcafe0000,
  parameter ADDR_W = 16,
  parameter DATA_BYTEW = 4,
  parameter ID_W = 4
) (
  input wire                        i_clk,
  input wire                        i_rst,

  // Signals ordered according to the document:
  // AMBA AXI and ACE Proctocol Specification
  // ARM IHI 0022D (ID102711)
  // IDs are included for interoperability with AXI4 (B1-124).

  // Write address channel signals.
  input  wire [ID_W-1:0]            i_axi_AWID,
  input  wire [ADDR_W-1:0]          i_axi_AWADDR,
  input  wire [2:0]                 i_axi_AWPROT,
  input  wire                       i_axi_AWVALID,
  output wire                       o_axi_AWREADY,

  // Write data channel signals.
  input  wire [(DATA_BYTEW*8)-1:0]  i_axi_WDATA,
  input  wire [DATA_BYTEW-1:0]      i_axi_WSTRB,
  input  wire                       i_axi_WVALID,
  output wire                       o_axi_WREADY,

  // Write response channel signals.
  output wire [ID_W-1:0]            o_axi_BID,
  output wire [1:0]                 o_axi_BRESP,
  output wire                       o_axi_BVALID,
  input  wire                       i_axi_BREADY,

  // Read address channel signals.
  input  wire [ID_W-1:0]            i_axi_ARID,
  input  wire [ADDR_W-1:0]          i_axi_ARADDR,
  input  wire [2:0]                 i_axi_ARPROT,
  input  wire                       i_axi_ARVALID,
  output wire                       o_axi_ARREADY,

  // Read data channel signals.
  output wire [ID_W-1:0]            o_axi_RID,
  output wire [(DATA_BYTEW*8)-1:0]  o_axi_RDATA,
  output wire [1:0]                 o_axi_RRESP,
  output wire                       o_axi_RVALID,
  input  wire                       i_axi_RREADY,

  // Probability control of undesirable behaviours.
  // '1 is rarely good (mostly bad), '0 is always good (never bad).
  input wire [PROB_W-1:0]           i_pr_aw_stall,
  input wire [PROB_W-1:0]           i_pr_w_stall,
  input wire [PROB_W-1:0]           i_pr_b_stall,
  input wire [PROB_W-1:0]           i_pr_ar_stall,
  input wire [PROB_W-1:0]           i_pr_r_stall,
  input wire [PROB_W-1:0]           i_pr_bresp_notokay,
  input wire [PROB_W-1:0]           i_pr_rresp_notokay,
  input wire [PROB_W-1:0]           i_pr_rddata_corrupt,

  // Activity indicators.
  output wire                       o_busy,
  output wire                       o_idle,
  output wire                       o_stall
);

`include "ambaSpec.vh"

localparam OFFSET_W = $clog2(N_MEM_WORD); // 10
localparam OFFSET_L = $clog2(DATA_BYTEW); // 2
localparam OFFSET_H = OFFSET_W + OFFSET_L - 1; // 11
localparam WFIFO_W = DATA_BYTEW*9;
localparam BFIFO_W = ID_W + 2;
localparam RFIFO_W = ID_W + 2 + (DATA_BYTEW*8);

// Hold the pseudo-randomly generated numbers which are compared
// against a threshold.
reg [PROB_W-1:0] rnd_aw_stall;
reg [PROB_W-1:0] rnd_w_stall;
reg [PROB_W-1:0] rnd_b_stall;
reg [PROB_W-1:0] rnd_ar_stall;
reg [PROB_W-1:0] rnd_r_stall;
reg [PROB_W-1:0] rnd_bresp_notokay;
reg [PROB_W-1:0] rnd_rresp_notokay;
reg [PROB_W-1:0] rnd_rddata_corrupt;

// Assert these signals when undesirable (bad) behaviour must happen.
wire do_aw_stall;
wire do_w_stall;
wire do_b_stall;
wire do_ar_stall;
wire do_r_stall;
wire do_bresp_notokay;
wire do_rresp_notokay;
wire do_rddata_corrupt;

wire wfifo_i_push;
wire wfifo_i_pop;
wire wfifo_o_empty;
wire wfifo_o_full;
wire wfifo_o_pushed;
wire wfifo_o_popped;
wire [WFIFO_W-1:0] wfifo_i_data;
wire [WFIFO_W-1:0] wfifo_o_data;
wire [(DATA_BYTEW*8)-1:0] wdata;
wire [3:0] wstrb;

wire bfifo_i_push;
wire bfifo_i_pop;
wire bfifo_o_empty;
wire bfifo_o_full;
wire bfifo_o_pushed;
wire bfifo_o_popped;
wire [BFIFO_W-1:0] bfifo_i_data;
wire [BFIFO_W-1:0] bfifo_o_data;
`dff_nocg_srst(reg, bkeepvld, i_clk, i_rst, 'd0)

wire rfifo_i_push;
wire rfifo_i_pop;
wire rfifo_o_empty;
wire rfifo_o_full;
wire rfifo_o_pushed;
wire rfifo_o_popped;
wire [RFIFO_W-1:0] rfifo_i_data;
wire [RFIFO_W-1:0] rfifo_o_data;
`dff_nocg_srst(reg, rkeepvld, i_clk, i_rst, 'd0)
reg [(DATA_BYTEW*8)-1:0] rdata;

// Slave memory.
reg [(DATA_BYTEW*8)-1:0] memory_m [N_MEM_WORD];

wire [OFFSET_W-1:0] awoffset;
wire [OFFSET_W-1:0] aroffset;
wire awdecerr;
wire ardecerr;
reg [1:0] bresp;
reg [1:0] rresp;

// {{{ Pseudo Random controls

`ifdef ABSTRACT_PRNG
  always @ (posedge i_clk) begin
                                                  /* verilator lint_off WIDTH */
    rnd_aw_stall       = $random;
    rnd_w_stall        = $random;
    rnd_b_stall        = $random;
    rnd_ar_stall       = $random;
    rnd_r_stall        = $random;
    rnd_bresp_notokay  = $random;
    rnd_rresp_notokay  = $random;
    rnd_rddata_corrupt = $random;
                                                  /* verilator lint_on  WIDTH */
  end
`else
  // Detect reset being removed to seed PRNG once.
  wire doSeed;
  resetDetect u_resetDetect (
    .i_clk            (i_clk),
    .i_rst            (i_rst),
    .o_wentInactive   (doSeed)
  );

  // NOTE: PRNG costs 192 flops per instance so share between all 8 probability
  // controls to keep synth small.
  // NOTE: Single non-configurable seed set used for repeatablity.
  wire [63:0] prngResult;
  prngXoroshiro128p u_prng (
    .i_clk      (i_clk),
    .i_rst      (i_rst),
    .i_cg       (1'b1), // unused
    .i_seedValid(doSeed),
    .i_seedS0   (64'd3141592654), // pi
    .i_seedS1   (64'd1618033989), // golden ratio
    .o_s0       (), // unused
    .o_s1       (), // unused

    .o_result   (prngResult)
  );

  // NOTE: PROB_W is restricted to 8 or less.
  always @* rnd_aw_stall       = prngResult[0*PROB_W +: PROB_W];
  always @* rnd_w_stall        = prngResult[1*PROB_W +: PROB_W];
  always @* rnd_b_stall        = prngResult[2*PROB_W +: PROB_W];
  always @* rnd_ar_stall       = prngResult[3*PROB_W +: PROB_W];
  always @* rnd_r_stall        = prngResult[4*PROB_W +: PROB_W];
  always @* rnd_bresp_notokay  = prngResult[5*PROB_W +: PROB_W];
  always @* rnd_rresp_notokay  = prngResult[6*PROB_W +: PROB_W];
  always @* rnd_rddata_corrupt = prngResult[7*PROB_W +: PROB_W];
`endif

assign do_aw_stall       = (i_pr_aw_stall       > rnd_aw_stall);
assign do_w_stall        = (i_pr_w_stall        > rnd_w_stall);
assign do_b_stall        = (i_pr_b_stall        > rnd_b_stall);
assign do_ar_stall       = (i_pr_ar_stall       > rnd_ar_stall);
assign do_r_stall        = (i_pr_r_stall        > rnd_r_stall);
assign do_bresp_notokay  = (i_pr_bresp_notokay  > rnd_bresp_notokay);
assign do_rresp_notokay  = (i_pr_rresp_notokay  > rnd_rresp_notokay);
assign do_rddata_corrupt = (i_pr_rddata_corrupt > rnd_rddata_corrupt);

// }}} Pseudo Random controls

// {{{ wfifo
fifo #(
  .WIDTH(WFIFO_W),
  .DEPTH(8)
) u_wfifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1), // unused

  .i_flush    (1'b0), // unused
  .i_push     (wfifo_i_push),
  .i_pop      (wfifo_i_pop),

  .i_data     (wfifo_i_data),
  .o_data     (wfifo_o_data),

  .o_empty    (wfifo_o_empty),
  .o_full     (wfifo_o_full),

  .o_pushed   (wfifo_o_pushed),
  .o_popped   (wfifo_o_popped),

  .o_wrptr    (), // unused
  .o_rdptr    (), // unused

  .o_valid    (), // unused
  .o_nEntries (), // unused

  .o_entries  ()  // unused
);
// }}} wfifo

// {{{ bfifo
fifo #(
  .WIDTH(BFIFO_W),
  .DEPTH(8)
) u_bfifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1), // unused

  .i_flush    (1'b0), // unused
  .i_push     (bfifo_i_push),
  .i_pop      (bfifo_i_pop),

  .i_data     (bfifo_i_data),
  .o_data     (bfifo_o_data),

  .o_empty    (bfifo_o_empty),
  .o_full     (bfifo_o_full),

  .o_pushed   (bfifo_o_pushed),
  .o_popped   (bfifo_o_popped),

  .o_wrptr    (), // unused
  .o_rdptr    (), // unused

  .o_valid    (), // unused
  .o_nEntries (), // unused

  .o_entries  ()  // unused
);
// }}} bfifo

// {{{ rfifo
fifo #(
  .WIDTH(RFIFO_W),
  .DEPTH(8)
) u_rfifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1), // unused

  .i_flush    (1'b0), // unused
  .i_push     (rfifo_i_push),
  .i_pop      (rfifo_i_pop),

  .i_data     (rfifo_i_data),
  .o_data     (rfifo_o_data),

  .o_empty    (rfifo_o_empty),
  .o_full     (rfifo_o_full),

  .o_pushed   (rfifo_o_pushed),
  .o_popped   (rfifo_o_popped),

  .o_wrptr    (), // unused
  .o_rdptr    (), // unused

  .o_valid    (), // unused
  .o_nEntries (), // unused

  .o_entries  ()  // unused
);
// }}} rfifo

assign wfifo_i_data = {i_axi_WDATA, i_axi_WSTRB};
assign bfifo_i_data = {i_axi_AWID, bresp};
assign rfifo_i_data = {i_axi_ARID, rresp, rdata};
assign {wdata, wstrb} = wfifo_o_data;
assign {o_axi_BID, o_axi_BRESP} = bfifo_o_data;
assign {o_axi_RID, o_axi_RRESP, o_axi_RDATA} = rfifo_o_data;

assign wfifo_i_push = (i_axi_WVALID && o_axi_WREADY) && !bfifo_i_push;
assign wfifo_i_pop  = !wfifo_o_empty && bfifo_i_push;

assign bfifo_i_push = i_axi_AWVALID && o_axi_AWREADY;
assign bfifo_i_pop  = o_axi_BVALID  && i_axi_BREADY;
assign rfifo_i_push = i_axi_ARVALID && o_axi_ARREADY;
assign rfifo_i_pop  = o_axi_RVALID  && i_axi_RREADY;

always @*
  if (!bkeepvld_q)
    bkeepvld_d = o_axi_BVALID && !i_axi_BREADY; // set
  else if (bfifo_i_pop)
    bkeepvld_d = 1'b0; // clr
  else
    bkeepvld_d = bkeepvld_q;

always @*
  if (!rkeepvld_q)
    rkeepvld_d = o_axi_RVALID && !i_axi_RREADY; // set
  else if (rfifo_i_pop)
    rkeepvld_d = 1'b0; // clr
  else
    rkeepvld_d = rkeepvld_q;

// Keep xVALID high until xREADY.
assign o_axi_BVALID = !bfifo_o_empty && (!do_b_stall || bkeepvld_q);
assign o_axi_RVALID = !rfifo_o_empty && (!do_r_stall || rkeepvld_q);

// Backpressure on request channels.
assign o_axi_AWREADY = !do_aw_stall && !bfifo_o_full;
assign o_axi_WREADY  = !do_w_stall  && !wfifo_o_full;
assign o_axi_ARREADY = !do_ar_stall && !rfifo_o_full;

// Address decode.
assign awoffset = i_axi_AWADDR[OFFSET_H:OFFSET_L];
assign aroffset = i_axi_ARADDR[OFFSET_H:OFFSET_L];
generate if (OFFSET_W < ADDR_W) begin
  assign awdecerr =
    i_axi_AWADDR[ADDR_W-1:OFFSET_H+1] != ADDR_BASE[ADDR_W-1:OFFSET_H+1];
  assign ardecerr =
    i_axi_ARADDR[ADDR_W-1:OFFSET_H+1] != ADDR_BASE[ADDR_W-1:OFFSET_H+1];
end else begin
  assign awdecerr = 1'b0;
  assign ardecerr = 1'b0;
end endgenerate

// AXI4lite doesn't support EXOKAY (2'b01).
// Choose DECERR (2'b11) when address is out of range.
// Choose between OKAY (2'b00) and SLVERR (2'b10) with probabilistic control.
always @*
  if (awdecerr)
    bresp = AXI_RESP_DECERR;
  else if (do_bresp_notokay)
    bresp = AXI_RESP_SLVERR;
  else
    bresp = AXI_RESP_OKAY;

always @*
  if (ardecerr)
    rresp = AXI_RESP_DECERR;
  else if (do_rresp_notokay)
    rresp = AXI_RESP_SLVERR;
  else
    rresp = AXI_RESP_OKAY;

// Write data to memory.
genvar i;
generate for (i = 0; i < DATA_BYTEW; i=i+1) begin : memoryWrite_b
  always @ (posedge i_clk)
    if (bfifo_i_push && !awdecerr && wstrb[i])
      memory_m[awoffset][i*8 +: 8] <= wdata[i*8 +: 8];

  // Initialise memory with random data.
  `ifndef VERILATOR
  `ifndef SYNTHESIS
  integer j;
  initial for (j = 0; j < N_MEM_WORD; j=j+1) begin
      memory_m[j][i*8 +: 8] = $urandom_range(255, 0);
  end
  `endif
  `endif
end : memoryWrite_b endgenerate

// Read data from memory.
always @* begin
  rdata = memory_m[aroffset];
  if (do_rddata_corrupt)
    // Flip a single bit to corrupt data.
    rdata = rdata ^ (1 << rnd_rddata_corrupt[$clog2(DATA_BYTEW*8)-1:0]);
end

assign o_busy = (!bfifo_o_empty || !rfifo_o_empty);

// Idle timeout.
// Assert o_idle after a fixed (small) number of cycles of inactivity.
`dff_nocg_srst(reg [3:0], idlecnt, i_clk, i_rst, 'd0)
always @*
  if (!bfifo_o_empty || !rfifo_o_empty)
    idlecnt_d = IDLE_TIMEOUT;
  else
    idlecnt_d = (idlecnt_q == '0) ? '0 : idlecnt_q - 1;

assign o_idle = !o_busy && (idlecnt_q == '0);

assign o_stall =
  (!bfifo_o_empty && do_b_stall) ||
  (!rfifo_o_empty && do_r_stall);

endmodule
