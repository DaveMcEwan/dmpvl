`include "dff.svh"

module axi4liteRandomMaster #(
  parameter PROB_W = 8,
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
  output wire [ID_W-1:0]            o_axi_AWID,
  output wire [ADDR_W-1:0]          o_axi_AWADDR,
  output wire [2:0]                 o_axi_AWPROT,
  output wire                       o_axi_AWVALID,
  input  wire                       i_axi_AWREADY,

  // Write data channel signals.
  output wire [(DATA_BYTEW*8)-1:0]  o_axi_WDATA,
  output wire [3:0]                 o_axi_WSTRB,
  output wire                       o_axi_WVALID,
  input  wire                       i_axi_WREADY,

  // Write response channel signals.
  input  wire [ID_W-1:0]            i_axi_BID,
  input  wire [1:0]                 i_axi_BRESP,
  input  wire                       i_axi_BVALID,
  output wire                       o_axi_BREADY,

  // Read address channel signals.
  output wire [ID_W-1:0]            o_axi_ARID,
  output wire [ADDR_W-1:0]          o_axi_ARADDR,
  output wire [2:0]                 o_axi_ARPROT,
  output wire                       o_axi_ARVALID,
  input  wire                       i_axi_ARREADY,

  // Read data channel signals.
  input  wire [ID_W-1:0]            i_axi_RID,
  input  wire [(DATA_BYTEW*8)-1:0]  i_axi_RDATA,
  input  wire [1:0]                 i_axi_RRESP,
  input  wire                       i_axi_RVALID,
  output wire                       o_axi_RREADY,

  // Probability control of undesirable behaviours.
  // '1 is rarely good (mostly bad), '0 is always good (never bad).
  input wire [PROB_W-1:0]           i_pr_aw_stall,
  input wire [PROB_W-1:0]           i_pr_w_stall,
  input wire [PROB_W-1:0]           i_pr_b_stall,
  input wire [PROB_W-1:0]           i_pr_ar_stall,
  input wire [PROB_W-1:0]           i_pr_r_stall
);

localparam AWFIFO_W = ID_W + ADDR_W;
localparam WFIFO_W = (DATA_BYTEW*8) + 4;
localparam ARFIFO_W = ID_W + ADDR_W;

// Hold the pseudo-randomly generated numbers which are compared against a
// threshold.
reg [PROB_W-1:0] rnd_aw_stall;
reg [PROB_W-1:0] rnd_w_stall;
reg [PROB_W-1:0] rnd_b_stall;
reg [PROB_W-1:0] rnd_ar_stall;
reg [PROB_W-1:0] rnd_r_stall;

// Hold pseudo-randomly generated numbers to be used as data somehow.
reg [ID_W-1:0]            rnd_awid;
reg [ADDR_W-1:0]          rnd_awaddr;
reg [(DATA_BYTEW*8)-1:0]  rnd_wdata;
reg [DATA_BYTEW-1:0]      rnd_wstrb;
reg [ID_W-1:0]            rnd_arid;
reg [ADDR_W-1:0]          rnd_araddr;

// Assert these signals when undesirable (bad) behaviour must happen.
wire do_aw_stall;
wire do_w_stall;
wire do_b_stall;
wire do_ar_stall;
wire do_r_stall;

wire awfifo_i_push;
wire awfifo_i_pop;
wire awfifo_o_empty;
wire awfifo_o_full;
wire awfifo_o_pushed;
wire awfifo_o_popped;
wire [AWFIFO_W-1:0] awfifo_i_data;
wire [AWFIFO_W-1:0] awfifo_o_data;
`dff_nocg_srst(reg, awkeepvld, i_clk, i_rst, 1'b0)

wire wfifo_i_push;
wire wfifo_i_pop;
wire wfifo_o_empty;
wire wfifo_o_full;
wire wfifo_o_pushed;
wire wfifo_o_popped;
wire [WFIFO_W-1:0] wfifo_i_data;
wire [WFIFO_W-1:0] wfifo_o_data;
`dff_nocg_srst(reg, wkeepvld, i_clk, i_rst, 1'b0)

wire arfifo_i_push;
wire arfifo_i_pop;
wire arfifo_o_empty;
wire arfifo_o_full;
wire arfifo_o_pushed;
wire arfifo_o_popped;
wire [ARFIFO_W-1:0] arfifo_i_data;
wire [ARFIFO_W-1:0] arfifo_o_data;
`dff_nocg_srst(reg, arkeepvld, i_clk, i_rst, 1'b0)

// {{{ Pseudo Random controls

`ifdef ABSTRACT_PRNG
  always @ (posedge i_clk) begin
                                                  /* verilator lint_off WIDTH */
    rnd_aw_stall    = $random;
    rnd_w_stall     = $random;
    rnd_b_stall     = $random;
    rnd_ar_stall    = $random;
    rnd_r_stall     = $random;

    rnd_awid        = $random;
    rnd_awaddr      = $random;
    rnd_wdata       = $random;
    rnd_wstrb       = $random;
    rnd_arid        = $random;
    rnd_araddr      = $random;
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

  // NOTE: PRNG costs 192 flops per instance so share between all 5 probability
  // controls and  to keep synth small.
  // NOTE: Single non-configurable seed set used for repeatablity.
  wire [63:0] prngResult;
  prngXoroshiro128p u_prng (
    .i_clk      (i_clk),
    .i_rst      (i_rst),
    .i_cg       (1'b1), // unused
    .i_seedValid(doSeed),
    .i_seedS0   (64'd1414213562), // sqrt 2
    .i_seedS1   (64'd2718281828), // e
    .o_s0       (), // unused
    .o_s1       (), // unused

    .o_result   (prngResult)
  );

  // NOTE: PROB_W is restricted to 9 or less.
  always @* rnd_aw_stall = prngResult[0*PROB_W +: PROB_W];
  always @* rnd_w_stall  = prngResult[1*PROB_W +: PROB_W];
  always @* rnd_b_stall  = prngResult[2*PROB_W +: PROB_W];
  always @* rnd_ar_stall = prngResult[3*PROB_W +: PROB_W];
  always @* rnd_r_stall  = prngResult[4*PROB_W +: PROB_W];

  // NOTE: The "random" address/data/id's will be correlated, but it's all only
  // pseudo-random anyway so does it really matter?
  always @* rnd_awid   = prngResult[0 +: ID_W];
  always @* rnd_arid   = prngResult[5 +: ID_W];
  always @* rnd_awaddr = prngResult[10 +: ADDR_W];
  always @* rnd_wstrb  = prngResult[15 +: DATA_BYTEW];
  always @* rnd_araddr = prngResult[20 +: ADDR_W];
  always @* rnd_wdata  = prngResult[25 +: (DATA_BYTEW*8)];
`endif

assign do_aw_stall = (i_pr_aw_stall > rnd_aw_stall);
assign do_w_stall  = (i_pr_w_stall  > rnd_w_stall);
assign do_b_stall  = (i_pr_b_stall  > rnd_b_stall);
assign do_ar_stall = (i_pr_ar_stall > rnd_ar_stall);
assign do_r_stall  = (i_pr_r_stall  > rnd_r_stall);

// }}} Pseudo Random controls

// {{{ awfifo
fifo #(
  .WIDTH(AWFIFO_W),
  .DEPTH(2)
) u_awfifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1), // unused

  .i_flush    (1'b0), // unused
  .i_push     (awfifo_i_push),
  .i_pop      (awfifo_i_pop),

  .i_data     (awfifo_i_data),
  .o_data     (awfifo_o_data),

  .o_empty    (awfifo_o_empty),
  .o_full     (awfifo_o_full),

  .o_pushed   (awfifo_o_pushed),
  .o_popped   (awfifo_o_popped),

  .o_wrptr    (), // unused
  .o_rdptr    (), // unused

  .o_valid    (), // unused
  .o_nEntries (), // unused

  .o_entries  ()  // unused
);
// }}} awfifo

// {{{ wfifo
fifo #(
  .WIDTH(WFIFO_W),
  .DEPTH(2)
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

// {{{ arfifo
fifo #(
  .WIDTH(ARFIFO_W),
  .DEPTH(2)
) u_arfifo_u (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1), // unused

  .i_flush    (1'b0), // unused
  .i_push     (arfifo_i_push),
  .i_pop      (arfifo_i_pop),

  .i_data     (arfifo_i_data),
  .o_data     (arfifo_o_data),

  .o_empty    (arfifo_o_empty),
  .o_full     (arfifo_o_full),

  .o_pushed   (arfifo_o_pushed),
  .o_popped   (arfifo_o_popped),

  .o_wrptr    (), // unused
  .o_rdptr    (), // unused

  .o_valid    (), // unused
  .o_nEntries (), // unused

  .o_entries  ()  // unused
);
// }}} arfifo

assign awfifo_i_data = {rnd_awid, rnd_awaddr};
assign {o_axi_AWID, o_axi_AWADDR} = awfifo_o_data;

assign wfifo_i_data = {rnd_wdata, rnd_wstrb};
assign {o_axi_WDATA, o_axi_WSTRB} = wfifo_o_data;

// Prevent write addr/data fifos from getting out of sync by always doing
// concurrent pushes to AW and W queues.
assign awfifo_i_push = !awfifo_o_full && !wfifo_o_full;
assign wfifo_i_push = awfifo_i_push;

assign awfifo_i_pop = o_axi_AWVALID && i_axi_AWREADY;

always @*
  if (!awkeepvld_q)
    awkeepvld_d = o_axi_AWVALID && !i_axi_AWREADY; // set
  else if (awfifo_i_pop)
    awkeepvld_d = 1'b0; // clr
  else
    awkeepvld_d = awkeepvld_q;

assign o_axi_AWVALID = !awfifo_o_empty && (!do_aw_stall || awkeepvld_q);

assign wfifo_i_pop = o_axi_WVALID && i_axi_WREADY;

always @*
  if (!wkeepvld_q)
    wkeepvld_d = o_axi_WVALID && !i_axi_WREADY; // set
  else if (wfifo_i_pop)
    wkeepvld_d = 1'b0; // clr
  else
    wkeepvld_d = wkeepvld_q;

assign o_axi_WVALID = !wfifo_o_empty && (!do_w_stall || wkeepvld_q);

assign arfifo_i_push = !arfifo_o_full; // Always try to queue more transactions.
assign arfifo_i_pop = o_axi_ARVALID && i_axi_ARREADY;

always @*
  if (!arkeepvld_q)
    arkeepvld_d = o_axi_ARVALID && !i_axi_ARREADY; // set
  else if (arfifo_i_pop)
    arkeepvld_d = 1'b0; // clr
  else
    arkeepvld_d = arkeepvld_q;

assign o_axi_ARVALID = !arfifo_o_empty && (!do_ar_stall || arkeepvld_q);

assign arfifo_i_data = {rnd_arid, rnd_araddr};
assign {o_axi_ARID, o_axi_ARADDR} = arfifo_o_data;

// Backpressure on reply channels.
// Currently replies are unused so the backpressure is arbitrary.
assign o_axi_BREADY = !do_b_stall;
assign o_axi_RREADY = !do_r_stall;

assign o_axi_AWPROT = 3'b000;
assign o_axi_ARPROT = 3'b000;

endmodule
