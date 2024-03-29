`include "dff.svh"

module correlator #(
  parameter MAX_WINDOW_LENGTH_EXP = 16,
  parameter MAX_SAMPLE_PERIOD_EXP = 15,
  parameter MAX_SAMPLE_JITTER_EXP = 8,
  parameter WINDOW_PRECISION      = 8, // 1 < p <= MAX_WINDOW_LENGTH_EXP
  parameter METRIC_PRECISION      = 16,
  parameter PKTFIFO_DEPTH         = 50
) (
  input wire          i_clk,
  input wire          i_rst,
  input wire          i_cg,

  output wire [7:0]   o_pktfifo_data,
  output wire         o_pktfifo_empty, // !valid
  input  wire         i_pktfifo_pop, // ready
  input  wire         i_pktfifo_flush,

  input  wire [$clog2(MAX_WINDOW_LENGTH_EXP+1)-1:0]   i_windowLengthExp,
  input  wire                                         i_windowShape,
  input  wire [$clog2(MAX_SAMPLE_PERIOD_EXP+1)-1:0]   i_samplePeriodExp,
  input  wire [$clog2(MAX_SAMPLE_JITTER_EXP+1)-1:0]   i_sampleJitterExp,
  input  wire [2:0]                                   i_pwmSelect,

  input  wire         i_wr_samplePeriod,

  input  wire [7:0]   i_jitterSeedByte,
  input  wire         i_jitterSeedValid,

  input  wire         i_x,
  input  wire         i_y,

  output wire [31:0]  o_pkt,
  output wire         o_pwm
);

genvar i;

localparam WINDOW_LENGTH_EXP_W      = $clog2(MAX_WINDOW_LENGTH_EXP+1);
localparam SAMPLE_PERIOD_EXP_W      = $clog2(MAX_SAMPLE_PERIOD_EXP+1);
localparam SAMPLE_JITTER_EXP_W      = $clog2(MAX_SAMPLE_JITTER_EXP+1);
localparam PWM_SELECT_W             = 3;

localparam WINDOW_SHAPE_RECTANGULAR = 1'd0;
localparam WINDOW_SHAPE_LOGDROP     = 1'd1;

localparam PWM_SELECT_WIN_NUM       = 3'd0;
localparam PWM_SELECT_COUNT_X       = 3'd1;
localparam PWM_SELECT_COUNT_Y       = 3'd2;
localparam PWM_SELECT_COUNT_ISECT   = 3'd3;
localparam PWM_SELECT_COUNT_SYMDIFF = 3'd4;
localparam PWM_SELECT_COV           = 3'd5;
localparam PWM_SELECT_DEP           = 3'd6;
localparam PWM_SELECT_HAM           = 3'd7;

localparam TIME_W = MAX_WINDOW_LENGTH_EXP; // Shorter convenience alias

// {{{ Generate sampling strobe

wire [MAX_SAMPLE_PERIOD_EXP:0] ctrlPeriodM1_wide = (1 << i_samplePeriodExp) - 1;
wire [MAX_SAMPLE_PERIOD_EXP-1:0] ctrlPeriodM1 = ctrlPeriodM1_wide[0 +: MAX_SAMPLE_PERIOD_EXP];

wire [MAX_SAMPLE_JITTER_EXP-1:0] ctrlJitter;
generate for (i = 0; i < MAX_SAMPLE_JITTER_EXP; i=i+1) begin
  assign ctrlJitter[i] = (i_sampleJitterExp == (i+1));
end endgenerate

wire sampleStrobeX, sampleStrobeY, counterStrobe;
wire [31:0] _unused_sampleStrobe_xoshiro128p;
strobe #(
  .CTRL_PERIOD_W    (MAX_SAMPLE_PERIOD_EXP),
  .CTRL_JITTER_W    (MAX_SAMPLE_JITTER_EXP),
  .N_STROBE         (2),
  .ENABLE_JITTER    (1)
) u_sampleStrobe (
  .i_clk              (i_clk),
  .i_rst              (i_rst),
  .i_cg               (i_cg),

  .i_ctrlPeriodM1     (ctrlPeriodM1),
  .i_ctrlJitter       (ctrlJitter),

  .i_jitterSeedByte   (i_jitterSeedByte),
  .i_jitterSeedValid  (i_jitterSeedValid),
  .o_jitterPrng       (_unused_sampleStrobe_xoshiro128p),

  .o_strobe           ({sampleStrobeX,sampleStrobeY})
);

`dff_cg_srst(reg, antiPhase, i_clk, i_cg, i_rst, 1'b0)
always @*
  if (i_wr_samplePeriod)
    antiPhase_d = 1'b1;
  else if (antiPhase_q && counterStrobe)
    antiPhase_d = 1'b0;
  else
    antiPhase_d = antiPhase_q;

wire [31:0] _unused_counterStrobe_xoshiro128p;
strobe #(
  .CTRL_PERIOD_W    (MAX_SAMPLE_PERIOD_EXP),
  .CTRL_JITTER_W    (MAX_SAMPLE_JITTER_EXP),
  .N_STROBE         (1),
  .ENABLE_JITTER    (0)
) u_counterStrobe (
  .i_clk              (i_clk),
  .i_rst              (i_rst),
  .i_cg               (i_cg),

  .i_ctrlPeriodM1     (antiPhase_q ? (ctrlPeriodM1 >> 1) : ctrlPeriodM1),
  .i_ctrlJitter       ('0),

  .i_jitterSeedByte   ('0),
  .i_jitterSeedValid  (1'b0),
  .o_jitterPrng       (_unused_counterStrobe_xoshiro128p),

  .o_strobe           (counterStrobe)
);


wire tDoWrap;
`dff_cg_srst(reg [TIME_W-1:0], t, i_clk, i_cg && counterStrobe, i_rst, '0)
always @* t_d = tDoWrap ? '0 : t_q + 1;

wire [MAX_WINDOW_LENGTH_EXP:0] tDoWrapVec;
generate for (i = 0; i <= MAX_WINDOW_LENGTH_EXP; i=i+1) begin
  if (i == 0) begin
    assign tDoWrapVec[0] = (i_windowLengthExp == 0);
  end else begin
    assign tDoWrapVec[i] = (i_windowLengthExp == i) && (&t_q[0 +: i]);
  end
end endgenerate
assign tDoWrap = |tDoWrapVec && counterStrobe;

`dff_cg_norst(reg, x, i_clk, i_cg && sampleStrobeX)
`dff_cg_norst(reg, y, i_clk, i_cg && sampleStrobeY)
always @* y_d = i_y;
always @* x_d = i_x;
`ifndef SYNTHESIS
initial x_q = '0;
initial y_q = '0;
`endif

// }}} Generate sampling strobe

// {{{ Correlation counters

wire [TIME_W-1:0] rect_countX;
wire [TIME_W-1:0] rect_countY;
wire [TIME_W-1:0] rect_countIsect;
wire [TIME_W-1:0] rect_countSymdiff;
corrCountRect #(
  .TIME_W  (TIME_W)
) u_winRect (
  .i_clk          (i_clk),
  .i_rst          (i_rst),
  .i_cg           (i_cg && counterStrobe),

  .i_x            (x_q),
  .i_y            (y_q),

  .o_countX       (rect_countX),
  .o_countY       (rect_countY),
  .o_countIsect   (rect_countIsect),
  .o_countSymdiff (rect_countSymdiff),

  .i_windowLengthExp (i_windowLengthExp),

  .i_zeroCounts   (tDoWrap)
);

localparam WINDOW_TIME_W = WINDOW_PRECISION + TIME_W - 1;
wire [WINDOW_TIME_W-1:0] logdrop_countX;
wire [WINDOW_TIME_W-1:0] logdrop_countY;
wire [WINDOW_TIME_W-1:0] logdrop_countIsect;
wire [WINDOW_TIME_W-1:0] logdrop_countSymdiff;
corrCountLogdrop #(
  .INCR_W  (WINDOW_PRECISION),
  .TIME_W  (TIME_W)
) u_winLogdrop (
  .i_clk          (i_clk),
  .i_rst          (i_rst),
  .i_cg           (i_cg && counterStrobe),

  .i_x            (x_q),
  .i_y            (y_q),

  .o_countX       (logdrop_countX),
  .o_countY       (logdrop_countY),
  .o_countIsect   (logdrop_countIsect),
  .o_countSymdiff (logdrop_countSymdiff),

  .i_windowLengthExp (i_windowLengthExp),

  .i_t            (t_q),
  .i_zeroCounts   (tDoWrap)
);

// }}} Correlation counters

wire pktfifo_push;
wire pktIdx_wrap;
`dff_upcounter(reg [2:0], pktIdx, i_clk, i_cg && pktfifo_push, i_rst || pktIdx_wrap)
assign pktIdx_wrap = i_cg &&
  (((pktIdx_q == 'd4) && pktfifo_push) || i_pktfifo_flush);

// {{{ Correlation metrics

`dff_cg_norst(reg [TIME_W-1:0], countX,       i_clk, i_cg && tDoWrap)
`dff_cg_norst(reg [TIME_W-1:0], countY,       i_clk, i_cg && tDoWrap)
`dff_cg_norst(reg [TIME_W-1:0], countIsect,   i_clk, i_cg && tDoWrap)
`dff_cg_norst(reg [TIME_W-1:0], countSymdiff, i_clk, i_cg && tDoWrap)
`ifndef SYNTHESIS
initial countX_q = '0;
initial countY_q = '0;
initial countIsect_q = '0;
initial countSymdiff_q = '0;
`endif

// Metric calculations only use top bits from the counters.
wire [METRIC_PRECISION-1:0] countX_narrow =
  countX_q[TIME_W-METRIC_PRECISION +: METRIC_PRECISION];
wire [METRIC_PRECISION-1:0] countY_narrow =
  countY_q[TIME_W-METRIC_PRECISION +: METRIC_PRECISION];
wire [METRIC_PRECISION-1:0] countIsect_narrow =
  countIsect_q[TIME_W-METRIC_PRECISION +: METRIC_PRECISION];
wire [METRIC_PRECISION-1:0] countSymdiff_narrow =
  countSymdiff_q[TIME_W-METRIC_PRECISION +: METRIC_PRECISION];

// NOTE: Lattice iCE40LP 16b multiplier path limited to ~60.5MHz.
// NOTE: Xilinx 7s DSP48E1 requires two pipeline stages to infer both MREG=1
// and PREG=1 because the multiplier outputs two partial products that need to
// be added together in the second (P) stage.
wire [2*METRIC_PRECISION-1:0] fullProdXY = countX_narrow * countY_narrow;
`dff_cg_norst(reg [METRIC_PRECISION-1:0], prodXY_partial, i_clk, i_cg && (pktIdx_q == 'd1))
`dff_cg_norst(reg [METRIC_PRECISION-1:0], prodXY, i_clk, i_cg && (pktIdx_q == 'd2))
always @* prodXY_partial_d = fullProdXY[METRIC_PRECISION-1:0];
always @* prodXY_d = prodXY_partial_q;

// NOTE: Lattice iCE40LP 16b divide path limited to ~16.5MHz.
//wire [METRIC_PRECISION-1:0] ratioIsectProdXY = prodXY_q / countIsect_narrow;
wire [METRIC_PRECISION-1:0] ratioIsectProdXY;
wire                        ratioIsectProdXY_o_done;
wire                        _unused_ratioIsectProdXY_o_busy;
wire [METRIC_PRECISION-1:0] _unused_ratioIsectProdXY_o_remainder;
dividerFsm #(
  .WIDTH          (METRIC_PRECISION),
  .ABSTRACT_MODEL (0)
) u_ratioIsectProdXY (
  .i_clk      (i_clk),
  .i_cg       (i_cg),
  .i_rst      (i_rst),

  .i_begin    (pktIdx_q == 'd3),
  .i_dividend (prodXY_q),
  .i_divisor  (countIsect_narrow),

  .o_busy     (_unused_ratioIsectProdXY_o_busy),
  .o_done     (ratioIsectProdXY_o_done),
  .o_quotient (ratioIsectProdXY),
  .o_remainder(_unused_ratioIsectProdXY_o_remainder)
);

// | 𝔼[X ⊙ Y] - 𝔼[X].𝔼[Y] |   =  𝔼[X ⊙ Y] - 𝔼[X].𝔼[Y]   : (𝔼[X ⊙ Y] > 𝔼[X].𝔼[Y])
//                               𝔼[X].𝔼[Y] - 𝔼[X ⊙ Y]   : otherwise
wire isectGtProdXY = (countIsect_narrow > prodXY_q);
wire [METRIC_PRECISION-1:0] diffIsectProdXY_A = countIsect_narrow - prodXY_q;
wire [METRIC_PRECISION-1:0] diffIsectProdXY_B = prodXY_q - countIsect_narrow;
wire [METRIC_PRECISION-1:0] absdiffIsectProdXY = isectGtProdXY ?
  diffIsectProdXY_A : diffIsectProdXY_B;

// Ċov(X, Y) := 4 . | 𝔼[X ⊙ Y] - 𝔼[X].𝔼[Y] |      ∊ [0, 1]
// NOTE: Fixed point format gives actual codomain of [0, 1) therefore:
//           = | 𝔼[X ⊙ Y] - 𝔼[X].𝔼[Y] | * 2**2    ∊ [0, 1)
`dff_cg_norst(reg [METRIC_PRECISION-1:0], metricCov, i_clk, i_cg && (pktIdx_q == 'd3))
always @* metricCov_d = absdiffIsectProdXY << 2;

// Ḋep(X, Y) := 1 - 𝔼[X].𝔼[Y] / 𝔼[X ⊙ Y]          ∊ [0, 1]
// NOTE: Fixed point format gives codomain of [0, 1), therefore the leading 1
// cannot be represented, therefore:
//           = ¬( 𝔼[X].𝔼[Y] / 𝔼[X ⊙ Y] )          ∊ [0, 1)
`dff_cg_norst(reg [METRIC_PRECISION-1:0], metricDep, i_clk, i_cg && ratioIsectProdXY_o_done)
always @* metricDep_d = ~ratioIsectProdXY;

// Ḣam(X, Y) := 1 - 𝔼[| X - Y |]                  ∊ [0, 1]
// NOTE: Fixed point format gives codomain of [0, 1), therefore the leading 1
// cannot be represented, and absdiff(X,Y) is equivalent to XOR in binary data
// therefore:
//           = ¬𝔼[X ⊙ Y]                          ∊ [0, 1)
`dff_cg_norst(reg [METRIC_PRECISION-1:0], metricHam, i_clk, i_cg && (pktIdx_q == 'd1))
always @* metricHam_d = ~countSymdiff_narrow;

// }}} Correlation metrics

// {{{ Packetize and queue data for recording

reg [7:0] pktfifo_i_data;
assign pktfifo_push = tDoWrap || (pktIdx_q != '0);
wire pktfifo_o_valid;
assign o_pktfifo_empty = !pktfifo_o_valid;
wire                                  _unused_pktfifo_o_notFull;
wire                                  _unused_pktfifo_o_pushed;
wire                                  _unused_pktfifo_o_popped;
wire [$clog2(PKTFIFO_DEPTH)-1:0]      _unused_pktfifo_o_wptr;
wire [$clog2(PKTFIFO_DEPTH)-1:0]      _unused_pktfifo_o_rptr;
wire [PKTFIFO_DEPTH-1:0]              _unused_pktfifo_o_validEntries;
wire [$clog2(PKTFIFO_DEPTH+1)-1:0]    _unused_pktfifo_o_nEntries;
wire [8*PKTFIFO_DEPTH-1:0]            _unused_pktfifo_o_entries;
fifoW1R1 #(
  .WIDTH          (8),
  .DEPTH          (PKTFIFO_DEPTH),
  .FLOPS_NOT_MEM  (0)
) u_pktfifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (i_cg),

  .i_flush    (i_pktfifo_flush),

  .i_data     (pktfifo_i_data),
  .i_valid    (pktfifo_push),
  .o_ready    (_unused_pktfifo_o_notFull),

  .o_data     (o_pktfifo_data),
  .o_valid    (pktfifo_o_valid),
  .i_ready    (i_pktfifo_pop),

  .o_pushed   (_unused_pktfifo_o_pushed),
  .o_popped   (_unused_pktfifo_o_popped),

  .o_wptr     (_unused_pktfifo_o_wptr),
  .o_rptr     (_unused_pktfifo_o_rptr),

  .o_validEntries (_unused_pktfifo_o_validEntries),
  .o_nEntries     (_unused_pktfifo_o_nEntries),

  .o_entries  (_unused_pktfifo_o_entries)
);

// Wrapping window counter to be used only to check that packets have not been
// dropped.
`dff_upcounter(reg [7:0], winNum, i_clk, i_cg && tDoWrap, i_rst)

always @*
  case (i_windowShape)
    WINDOW_SHAPE_LOGDROP: begin
      countX_d        = logdrop_countX[WINDOW_TIME_W-TIME_W +: TIME_W];
      countY_d        = logdrop_countY[WINDOW_TIME_W-TIME_W +: TIME_W];
      countIsect_d    = logdrop_countIsect[WINDOW_TIME_W-TIME_W +: TIME_W];
      countSymdiff_d  = logdrop_countSymdiff[WINDOW_TIME_W-TIME_W +: TIME_W];
    end
    default: begin // WINDOW_SHAPE_RECTANGULAR
      countX_d        = rect_countX;
      countY_d        = rect_countY;
      countIsect_d    = rect_countIsect;
      countSymdiff_d  = rect_countSymdiff;
    end
  endcase

`dff_cg_norst(reg [4*8-1:0], pkt, i_clk, i_cg && tDoWrap)
// Only the 8 most significant bits of the counters is reported
always @* pkt_d = {
  countSymdiff_d[TIME_W-8 +: 8],
  countIsect_d[TIME_W-8 +: 8],
  countY_d[TIME_W-8 +: 8],
  countX_d[TIME_W-8 +: 8]
};

always @*
  case (pktIdx_q)
    3'd1:     pktfifo_i_data = pkt_q[8*0 +: 8];
    3'd2:     pktfifo_i_data = pkt_q[8*1 +: 8];
    3'd3:     pktfifo_i_data = pkt_q[8*2 +: 8];
    3'd4:     pktfifo_i_data = pkt_q[8*3 +: 8];
    default:  pktfifo_i_data = winNum_q;
  endcase

assign o_pkt = pkt_q;

// }}} Packetize and queue data for recording

// {{{ Pulse-Width (or Delta-Sigma) Modulation

reg [7:0] pwmCtrl;
always @*
  case (i_pwmSelect)
    PWM_SELECT_COUNT_X:         pwmCtrl = pkt_q[8*0 +: 8];
    PWM_SELECT_COUNT_Y:         pwmCtrl = pkt_q[8*1 +: 8];
    PWM_SELECT_COUNT_ISECT:     pwmCtrl = pkt_q[8*2 +: 8];
    PWM_SELECT_COUNT_SYMDIFF:   pwmCtrl = pkt_q[8*3 +: 8];
    PWM_SELECT_COV:             pwmCtrl = metricCov_q[METRIC_PRECISION-8 +: 8];
    PWM_SELECT_DEP:             pwmCtrl = metricDep_q[METRIC_PRECISION-8 +: 8];
    PWM_SELECT_HAM:             pwmCtrl = metricHam_q[METRIC_PRECISION-8 +: 8];
    default:  pwmCtrl = winNum_q; // PWM_SELECT_WIN_NUM
  endcase

wire [7:0] _unused_pwm_o_acc;
pwm #(
  .WIDTH  (8),
  .ARCH   (1) // ΔΣ for smoother DC offset
) u_pwm (
  .i_clk    (i_clk),
  .i_rst    (i_rst),
  .i_cg     (i_cg),

  .i_x      (pwmCtrl),
  .o_acc    (_unused_pwm_o_acc),
  .o_y      (o_pwm)
);

// }}} Pulse-Width (or Delta-Sigma) Modulation

endmodule
