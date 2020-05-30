`include "dff.vh"

module correlator #(
  parameter LOGDROP_PRECISION = 20, // >= MAX_WINDOW_LENGTH_EXP
  parameter MAX_WINDOW_LENGTH_EXP = 20,
  parameter MAX_SAMPLE_RATE_NEGEXP = 15,
  parameter MAX_SAMPLE_JITTER_EXP = 8
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

genvar i;

wire [7:0]        pktfifo_o_data;
wire              pktfifo_o_empty;
wire              pktfifo_i_pop;

wire [$clog2(MAX_WINDOW_LENGTH_EXP)-1:0]    windowLengthExp;
wire                                        windowShape;
wire [$clog2(MAX_SAMPLE_RATE_NEGEXP)-1:0]   sampleRateNegExp;
wire                                        sampleMode;
wire [$clog2(MAX_SAMPLE_JITTER_EXP)-1:0]    sampleJitterNegExp;
wire [MAX_SAMPLE_JITTER_EXP-1:0]            prngJitterValue;

bpReg #(
  .LOGDROP_PRECISION        (LOGDROP_PRECISION),
  .MAX_WINDOW_LENGTH_EXP    (MAX_WINDOW_LENGTH_EXP),
  .MAX_SAMPLE_RATE_NEGEXP   (MAX_SAMPLE_RATE_NEGEXP),
  .MAX_SAMPLE_JITTER_EXP    (MAX_SAMPLE_JITTER_EXP)
) u_bpReg (
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

  .o_prngJitterValue        (prngJitterValue),

  .i_bp_data   (i_bp_data),
  .i_bp_valid  (i_bp_valid),
  .o_bp_ready  (o_bp_ready),

  .o_bp_data   (o_bp_data),
  .o_bp_valid  (o_bp_valid),
  .i_bp_ready  (i_bp_ready)
);

reg [7:0] pktfifo_i_data;
wire pktfifo_i_push = tDoWrap || (pktIdx_q != 3'd0);
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
) u_pktfifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1),

  .i_flush    (1'b0), // TODO: Flush register for recovery.
  .i_push     (pktfifo_i_push),
  .i_pop      (pktfifo_i_pop),

  .i_data     (pktfifo_i_data),
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

`dff_upcounter(reg [MAX_SAMPLE_RATE_NEGEXP-1:0], sampleCntr, i_clk, i_cg, i_rst)
wire [MAX_SAMPLE_RATE_NEGEXP:0] sampleTickVec = {sampleCntr_q, 1'b1};
wire sampleTick = sampleTickVec[sampleRateNegExp] && (prngJitterValue == '0);
// TODO: That isn't right at all!

`dff_cg_srst(reg [MAX_WINDOW_LENGTH_EXP-1:0], t, i_clk, sampleTick, i_rst, '0)
always @* t_d = tDoWrap ? '0 : t_q + 1;

wire [MAX_WINDOW_LENGTH_EXP-1:0] tDoWrapVec;
wire [MAX_WINDOW_LENGTH_EXP-1:0] tScaledVec [MAX_WINDOW_LENGTH_EXP];
generate for (i = 0; i < MAX_WINDOW_LENGTH_EXP; i=i+1) begin
  if (i == 0) begin
    assign tDoWrapVec[0] = (windowLengthExp == 0);
    assign tScaledVec[0] = '0;
  end else begin
    assign tDoWrapVec[i] = (windowLengthExp == i) && (&t_q[0 +: i]);
    assign tScaledVec[i] = t_q << i;
  end
end endgenerate
wire tDoWrap = |tDoWrapVec;
`dff_cg_srst(reg [MAX_WINDOW_LENGTH_EXP-1:0], tScaled, i_clk, i_cg, i_rst, '0)
always @* tScaled_d = tScaledVec[windowLengthExp];

wire [MAX_WINDOW_LENGTH_EXP-1:0] rect_countX;
wire [MAX_WINDOW_LENGTH_EXP-1:0] rect_countY;
wire [MAX_WINDOW_LENGTH_EXP-1:0] rect_countIsect;
wire [MAX_WINDOW_LENGTH_EXP-1:0] rect_countSymdiff;
corrCountRect #(
  .TIME_W  (MAX_WINDOW_LENGTH_EXP)
) u_winRect (
  .i_clk          (i_clk),
  .i_rst          (i_rst),
  .i_cg           (sampleTick),

  .i_x            (i_x),
  .i_y            (i_y),

  .o_countX       (rect_countX),
  .o_countY       (rect_countY),
  .o_countIsect   (rect_countIsect),
  .o_countSymdiff (rect_countSymdiff),

  .i_zeroCounts   (tDoWrap)
);

// NOTE: Window coefficient is 1 sample out of of phase in order to meet timing.
// Therefore the X and Y inputs are also flopped.
// As winNum is pushed into the fifo before any results this is okay.
`dff_cg_norst(reg, x, i_clk, i_cg)
`dff_cg_norst(reg, y, i_clk, i_cg)
always @* y_d = i_y;
always @* x_d = i_x;

localparam LOGDROP_DATA_W = LOGDROP_PRECISION + MAX_WINDOW_LENGTH_EXP;
wire [LOGDROP_DATA_W-1:0] logdrop_countX;
wire [LOGDROP_DATA_W-1:0] logdrop_countY;
wire [LOGDROP_DATA_W-1:0] logdrop_countIsect;
wire [LOGDROP_DATA_W-1:0] logdrop_countSymdiff;
corrCountLogdrop #(
  .DATA_W  (LOGDROP_DATA_W),
  .TIME_W  (MAX_WINDOW_LENGTH_EXP)
) u_winLogdrop (
  .i_clk          (i_clk),
  .i_rst          (i_rst),
  .i_cg           (sampleTick),

  .i_x            (x_q),
  .i_y            (y_q),

  .o_countX       (logdrop_countX),
  .o_countY       (logdrop_countY),
  .o_countIsect   (logdrop_countIsect),
  .o_countSymdiff (logdrop_countSymdiff),

  .i_t            (tScaled_q),
  .i_zeroCounts   (tDoWrap)
);

// Wrapping window counter to be used only to check that packets have not been
// dropped.
`dff_upcounter(reg [7:0], winNum, i_clk, tDoWrap, i_rst)

// Only the 8 most significant bits of the counters is reported
wire [7:0] pkt_countX = windowShape ?
  logdrop_countX[LOGDROP_DATA_W-8 +: 8] :
  rect_countX[MAX_WINDOW_LENGTH_EXP-8 +: 8];

wire [7:0] pkt_countY = windowShape ?
  logdrop_countY[LOGDROP_DATA_W-8 +: 8] :
  rect_countY[MAX_WINDOW_LENGTH_EXP-8 +: 8];

wire [7:0] pkt_countIsect = windowShape ?
  logdrop_countIsect[LOGDROP_DATA_W-8 +: 8] :
  rect_countIsect[MAX_WINDOW_LENGTH_EXP-8 +: 8];

wire [7:0] pkt_countSymdiff = windowShape ?
  logdrop_countSymdiff[LOGDROP_DATA_W-8 +: 8] :
  rect_countSymdiff[MAX_WINDOW_LENGTH_EXP-8 +: 8];

wire pktIdx_wrap = (pktIdx_q == 3'd4) && pktfifo_i_push;
`dff_upcounter(reg [2:0], pktIdx, i_clk, pktfifo_i_push, i_rst || pktIdx_wrap)

always @*
  case (pktIdx_q)
    3'd1:     pktfifo_i_data = pkt_countX;
    3'd2:     pktfifo_i_data = pkt_countY;
    3'd3:     pktfifo_i_data = pkt_countIsect;
    3'd4:     pktfifo_i_data = pkt_countSymdiff;
    default:  pktfifo_i_data = winNum_q;
  endcase

endmodule
