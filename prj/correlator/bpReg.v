`include "dff.vh"

/* BytePipe interface, indended to sit on top of USB for register access.
Unpack the register map to wires.
*/
module bpReg #(
  parameter PRECISION = 8,
  parameter METRIC_A = 3,
  parameter METRIC_B = 4,
  parameter MAX_N_INPUTS = 5,
  parameter MAX_WINDOW_LENGTH_EXP = 31,
  parameter MAX_SAMPLE_RATE_NEGEXP = 31,
  parameter MAX_SAMPLE_JITTER_NEGEXP = 31
) (
  input wire          i_clk,
  input wire          i_rst,
  input wire          i_cg,

  output wire [$clog2(MAX_N_INPUTS)-1:0]              o_reg_nInputs,
  output wire [$clog2(MAX_WINDOW_LENGTH_EXP)-1:0]     o_reg_windowLengthExp,
  output wire                                         o_reg_windowShape,
  output wire [$clog2(MAX_SAMPLE_RATE_NEGEXP)-1:0]    o_reg_sampleRateNegExp,
  output wire                                         o_reg_sampleMode,
  output wire [$clog2(MAX_SAMPLE_JITTER_NEGEXP)-1:0]  o_reg_sampleJitterNegExp,

  input  wire [7:0]   i_bp_data,
  input  wire         i_bp_valid,
  output wire         o_bp_ready,

  output wire [7:0]   o_bp_data,
  output wire         o_bp_valid,
  input  wire         i_bp_ready
);

wire in_accepted = i_bp_valid && o_bp_ready;
wire out_accepted = o_bp_valid && i_bp_ready;

`dff_cg_srst(reg, wr, i_clk, i_cg, i_rst, '0)
`dff_cg_srst(reg, rd, i_clk, i_cg, i_rst, '0)

wire txnBegin = !wr_q && in_accepted;
wire wrBegin = txnBegin && i_bp_data[7];
wire wrEnd = wr_q && in_accepted;
wire rdBegin = (txnBegin && !wrBegin) || wrEnd;
wire rdEnd = out_accepted;

always @*
  if      (wrBegin) wr_d = 1'b1;
  else if (wrEnd)   wr_d = 1'b0;
  else              wr_d = wr_q;

always @*
  if      (rdBegin) rd_d = 1'b1;
  else if (rdEnd)   rd_d = 1'b0;
  else              rd_d = rd_q;

localparam ADDR_W = 4;
`dff_cg_srst(reg [ADDR_W-1:0], addr, i_clk, i_cg && txnBegin, i_rst, '0)
always @* addr_d = i_bp_data[ADDR_W-1:0];

// Address for all regs.
localparam ADDR_PRECISION                 = 4'd0;
localparam ADDR_METRIC_A                  = 4'd1;
localparam ADDR_METRIC_B                  = 4'd2;
localparam ADDR_MAX_N_INPUTS              = 4'd3;
localparam ADDR_MAX_WINDOW_LENGTH_EXP     = 4'd4;
localparam ADDR_MAX_SAMPLE_RATE_NEGEXP    = 4'd5;
localparam ADDR_MAX_SAMPLE_JITTER_NEGEXP  = 4'd6;
localparam ADDR_N_INPUTS                  = 4'd7;
localparam ADDR_WINDOW_LENGTH_EXP         = 4'd8;
localparam ADDR_WINDOW_SHAPE              = 4'd9;
localparam ADDR_SAMPLE_RATE_NEGEXP        = 4'd10;
localparam ADDR_SAMPLE_MODE               = 4'd11;
localparam ADDR_SAMPLE_JITTER_NEGEXP      = 4'd12;

// Write-enable for RW regs.
wire wr_nInputs             = wrEnd && (addr_q == ADDR_N_INPUTS);
wire wr_windowLengthExp     = wrEnd && (addr_q == ADDR_N_INPUTS);
wire wr_windowShape         = wrEnd && (addr_q == ADDR_N_INPUTS);
wire wr_sampleRateNegExp    = wrEnd && (addr_q == ADDR_N_INPUTS);
wire wr_sampleMode          = wrEnd && (addr_q == ADDR_N_INPUTS);
wire wr_sampleJitterNegExp  = wrEnd && (addr_q == ADDR_N_INPUTS);

// Widths and value enumerations.
localparam N_INPUTS_W               = $clog2(MAX_N_INPUTS);
localparam WINDOW_LENGTH_EXP_W      = $clog2(MAX_WINDOW_LENGTH_EXP);
localparam WINDOW_SHAPE_RECTANGULAR = 1'd0;
localparam WINDOW_SHAPE_LOGDROP     = 1'd1;
localparam SAMPLE_RATE_NEGEXP_W     = $clog2(MAX_SAMPLE_RATE_NEGEXP);
localparam SAMPLE_MODE_NONJITTER    = 1'd0;
localparam SAMPLE_MODE_NONPERIODIC  = 1'd1;
localparam SAMPLE_JITTER_NEGEXP_W   = $clog2(MAX_SAMPLE_JITTER_NEGEXP);

`dff_cg_srst(reg [N_INPUTS_W-1:0],             nInputs,            i_clk, i_cg && wr_nInputs,            i_rst, '0)
`dff_cg_srst(reg [WINDOW_LENGTH_EXP_W-1:0],    windowLengthExp,    i_clk, i_cg && wr_windowLengthExp,    i_rst, '0)
`dff_cg_srst(reg,                              windowShape,        i_clk, i_cg && wr_windowShape,        i_rst, '0)
`dff_cg_srst(reg [SAMPLE_RATE_NEGEXP_W-1:0],   sampleRateNegExp,   i_clk, i_cg && wr_sampleRateNegExp,   i_rst, '0)
`dff_cg_srst(reg,                              sampleMode,         i_clk, i_cg && wr_sampleMode,         i_rst, '0)
`dff_cg_srst(reg [SAMPLE_JITTER_NEGEXP_W-1:0], sampleJitterNegExp, i_clk, i_cg && wr_sampleJitterNegExp, i_rst, '0)
always @* nInputs_d             = i_bp_data[N_INPUTS_W-1:0];
always @* windowLengthExp_d     = i_bp_data[WINDOW_LENGTH_EXP_W-1:0];
always @* windowShape_d         = i_bp_data[0];
always @* sampleRateNegExp_d    = i_bp_data[SAMPLE_RATE_NEGEXP_W-1:0];
always @* sampleMode_d          = i_bp_data[0];
always @* sampleJitterNegExp_d  = i_bp_data[SAMPLE_JITTER_NEGEXP_W-1:0];

// Expose non-static (RW) regs as wires.
assign o_reg_nInputs            = nInputs_q;
assign o_reg_windowLengthExp    = windowLengthExp_q;
assign o_reg_windowShape        = windowShape_q;
assign o_reg_sampleRateNegExp   = sampleRateNegExp_q;
assign o_reg_sampleMode         = sampleMode_q;
assign o_reg_sampleJitterNegExp = sampleJitterNegExp_q;

`dff_cg_srst(reg [7:0], rdData, i_clk, i_cg && rdBegin, i_rst, '0)
always @*
  case (addr_q)
    // RO static
    ADDR_PRECISION:                rdData_d = PRECISION;
    ADDR_METRIC_A:                 rdData_d = METRIC_A;
    ADDR_METRIC_B:                 rdData_d = METRIC_B;
    ADDR_MAX_N_INPUTS:             rdData_d = MAX_N_INPUTS;
    ADDR_MAX_WINDOW_LENGTH_EXP:    rdData_d = MAX_WINDOW_LENGTH_EXP;
    ADDR_MAX_SAMPLE_RATE_NEGEXP:   rdData_d = MAX_SAMPLE_RATE_NEGEXP;
    ADDR_MAX_SAMPLE_JITTER_NEGEXP: rdData_d = MAX_SAMPLE_JITTER_NEGEXP;
                                                  /* verilator lint_off WIDTH */
    // RW
    ADDR_N_INPUTS:                 rdData_d = nInputs_q;
    ADDR_WINDOW_LENGTH_EXP:        rdData_d = windowLengthExp_q;
    ADDR_WINDOW_SHAPE:             rdData_d = windowShape_q;
    ADDR_SAMPLE_RATE_NEGEXP:       rdData_d = sampleRateNegExp_q;
    ADDR_SAMPLE_MODE:              rdData_d = sampleMode_q;
    ADDR_SAMPLE_JITTER_NEGEXP:     rdData_d = sampleJitterNegExp_q;
                                                  /* verilator lint_on  WIDTH */
    default:                       rdData_d = '0;
  endcase

// Backpressure goes straight through so destination controls all flow, so the
// host must keep accepting data.
assign o_bp_ready = i_bp_ready;

assign o_bp_data = rdData_q;
assign o_bp_valid = rd_q;

endmodule
