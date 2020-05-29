`include "dff.vh"

module correlator #(
  parameter PRECISION = 20,
  parameter MAX_SAMPLE_RATE_NEGEXP = 15,
  parameter MAX_SAMPLE_JITTER_NEGEXP = 14
) (
  input wire          i_clk,
  input wire          i_rst,
  input wire          i_cg,

  input  wire         i_x,
  input  wire         i_y,

  input  wire [7:0]   i_bp_data,
  input  wire         i_bp_valid,
  output wire         o_bp_ready,

  output wire [7:0]   o_bp_data,
  output wire         o_bp_valid,
  input  wire         i_bp_ready
);

wire [7:0]        pktfifo_o_data;
wire              pktfifo_o_empty;
wire              pktfifo_i_pop;

wire [$clog2(PRECISION)-1:0]                 windowLengthExp;
wire                                         windowShape;
wire [$clog2(MAX_SAMPLE_RATE_NEGEXP)-1:0]    sampleRateNegExp;
wire                                         sampleMode;
wire [$clog2(MAX_SAMPLE_JITTER_NEGEXP)-1:0]  sampleJitterNegExp;

bpReg u_bpReg (
  .i_clk              (i_clk),
  .i_rst              (i_rst),
  .i_cg               (1'b1),

  .i_pktfifo_data   (pktfifo_o_data),
  .i_pktfifo_empty  (pktfifo_o_empty),
  .o_pktfifo_pop    (pktfifo_i_pop),

  .o_reg_windowLengthExp    (windowLengthExp),
  .o_reg_windowShape        (windowShape),
  .o_reg_sampleRateNegExp   (sampleRateNegExp),
  .o_reg_sampleMode         (sampleMode),
  .o_reg_sampleJitterNegExp (sampleJitterNegExp),

  .i_bp_data   (i_bp_data),
  .i_bp_valid  (i_bp_valid),
  .o_bp_ready  (o_bp_ready),

  .o_bp_data   (o_bp_data),
  .o_bp_valid  (o_bp_valid),
  .i_bp_ready  (i_bp_ready)
);

wire              _unused_pktfifo_o_full;
wire              _unused_pktfifo_o_pushed;
wire              _unused_pktfifo_o_popped;
wire [5:0]        _unused_pktfifo_o_wrptr;
wire [5:0]        _unused_pktfifo_o_rdptr;
wire [49:0]       _unused_pktfifo_o_valid;
wire [5:0]        _unused_pktfifo_o_nEntries;
wire [8*50-1:0]   _unused_pktfifo_o_entries;
fifo #(
  .WIDTH          (8),
  .DEPTH          (50),
  .FLOPS_NOT_MEM  (0)
) u_fifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1),

  .i_flush    (1'b0), // TODO: Flush register for recovery.
  .i_push     (1'b1), // TODO
  .i_pop      (pktfifo_i_pop),

  .i_data     (8'd55), // TODO
  .o_data     (pktfifo_o_data),

  .o_empty    (pktfifo_o_empty),
  .o_full     (_unused_pktfifo_o_full),

  .o_pushed   (_unused_pktfifo_o_pushed),
  .o_popped   (_unused_pktfifo_o_popped),

  .o_wrptr    (_unused_pktfifo_o_wrptr),
  .o_rdptr    (_unused_pktfifo_o_rdptr),

  .o_valid    (_unused_pktfifo_o_valid),
  .o_nEntries (_unused_pktfifo_o_nEntries),

  .o_entries  (_unused_pktfifo_o_entries)
);

endmodule
