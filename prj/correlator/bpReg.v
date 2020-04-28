`include "dff.vh"

/* BytePipe interface, indended to sit on top of USB for register access.
Unpack the register map to wires.
*/
module bpReg #(
  parameter VALUE0 = 8'd0, // in {0x00..0xff}. Arbitrary value read from location 0.
  parameter PRECISION = 8,
  parameter METRIC_A = 3, // {1:Cls, 2:Cos, 3:Cov, 4:Dep, 5:Ham, 6:Tmt}
  parameter METRIC_B = 4, // {1:Cls, 2:Cos, 3:Cov, 4:Dep, 5:Ham, 6:Tmt}
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

// Address for all regs.
localparam N_REG = 13;
localparam ADDR_REG_LO = 1;
localparam ADDR_REG_HI = ADDR_REG_LO + N_REG - 1;
localparam ADDR_PRECISION                 = ADDR_REG_LO + 0;
localparam ADDR_METRIC_A                  = ADDR_REG_LO + 1;
localparam ADDR_METRIC_B                  = ADDR_REG_LO + 2;
localparam ADDR_MAX_N_INPUTS              = ADDR_REG_LO + 3;
localparam ADDR_MAX_WINDOW_LENGTH_EXP     = ADDR_REG_LO + 4;
localparam ADDR_MAX_SAMPLE_RATE_NEGEXP    = ADDR_REG_LO + 5;
localparam ADDR_MAX_SAMPLE_JITTER_NEGEXP  = ADDR_REG_LO + 6;
localparam ADDR_N_INPUTS                  = ADDR_REG_LO + 7;
localparam ADDR_WINDOW_LENGTH_EXP         = ADDR_REG_LO + 8;
localparam ADDR_WINDOW_SHAPE              = ADDR_REG_LO + 9;
localparam ADDR_SAMPLE_RATE_NEGEXP        = ADDR_REG_LO + 10;
localparam ADDR_SAMPLE_MODE               = ADDR_REG_LO + 11;
localparam ADDR_SAMPLE_JITTER_NEGEXP      = ADDR_REG_LO + 12;

localparam N_LOC = N_REG+1; // Registers plus burst@0.
localparam ADDR_W = $clog2(N_LOC);

localparam VALUE0_ = VALUE0; // Localparam for bit-slicing.
wire [7:0] value0 = VALUE0_[7:0];

`dff_cg_srst(reg, wr, i_clk, i_cg, i_rst, '0) // 1b FSM
`dff_cg_srst(reg, rd, i_clk, i_cg, i_rst, '0) // 1b FSM
`dff_cg_norst(reg [6:0], addr, i_clk, i_cg)
`dff_cg_srst(reg [7:0], burst, i_clk, i_cg, i_rst, '0) // 8b downcounter
`dff_cg_norst(reg [7:0], rdData, i_clk, i_cg && rd_d)

// IO aliases
wire in_accepted = i_bp_valid && o_bp_ready;
wire out_accepted = o_bp_valid && i_bp_ready;
wire cmdWr = i_bp_data[7];
wire cmdRd = !i_bp_data[7];
wire [6:0] cmdAddr = i_bp_data[6:0];

wire txnBegin = !wr_q && in_accepted;
wire inBurst = (burst_q != '0) && (addr_q != '0);
wire inBurstWr = inBurst && wr_q;
wire inBurstRd = inBurst && rd_q;
wire doWrite = wr_q && in_accepted;

wire [ADDR_W-1:0] rdAddr = addr_q[ADDR_W-1:0];
wire addrInRange = (ADDR_REG_HI[6:0] >= addr_q);

wire wrSet = txnBegin && cmdWr;
wire wrClr = doWrite && !inBurst;
wire rdSet = (txnBegin && cmdRd) || wrClr;
wire rdClr = out_accepted && !inBurst;
wire burstInit = doWrite && (addr_q == '0);
wire burstDecr = (inBurstWr && in_accepted) || (inBurstRd && out_accepted);

always @*
  if      (wrSet) wr_d = 1'b1;
  else if (wrClr) wr_d = 1'b0;
  else            wr_d = wr_q;

always @*
  if      (rdSet) rd_d = 1'b1;
  else if (rdClr) rd_d = 1'b0;
  else            rd_d = rd_q;

always @* addr_d = txnBegin ?  cmdAddr : addr_q;

always @*
  if      (burstInit) burst_d = i_bp_data;
  else if (burstDecr) burst_d = burst_q - 8'd1;
  else                burst_d = burst_q;

// Write-enable for RW regs.
wire doWriteReg = i_cg && wrClr && addrInRange;
wire wr_nInputs             = doWriteReg && (addr_q == ADDR_N_INPUTS);
wire wr_windowLengthExp     = doWriteReg && (addr_q == ADDR_WINDOW_LENGTH_EXP);
wire wr_windowShape         = doWriteReg && (addr_q == ADDR_WINDOW_SHAPE);
wire wr_sampleRateNegExp    = doWriteReg && (addr_q == ADDR_SAMPLE_RATE_NEGEXP);
wire wr_sampleMode          = doWriteReg && (addr_q == ADDR_SAMPLE_MODE);
wire wr_sampleJitterNegExp  = doWriteReg && (addr_q == ADDR_SAMPLE_JITTER_NEGEXP);

// Widths and value enumerations.
localparam N_INPUTS_W               = $clog2(MAX_N_INPUTS);
localparam WINDOW_LENGTH_EXP_W      = $clog2(MAX_WINDOW_LENGTH_EXP);
localparam WINDOW_SHAPE_RECTANGULAR = 1'd0;
localparam WINDOW_SHAPE_LOGDROP     = 1'd1;
localparam SAMPLE_RATE_NEGEXP_W     = $clog2(MAX_SAMPLE_RATE_NEGEXP);
localparam SAMPLE_MODE_NONJITTER    = 1'd0;
localparam SAMPLE_MODE_NONPERIODIC  = 1'd1;
localparam SAMPLE_JITTER_NEGEXP_W   = $clog2(MAX_SAMPLE_JITTER_NEGEXP);

`dff_cg_srst(reg [N_INPUTS_W-1:0],             nInputs,            i_clk, wr_nInputs,            i_rst, '0)
`dff_cg_srst(reg [WINDOW_LENGTH_EXP_W-1:0],    windowLengthExp,    i_clk, wr_windowLengthExp,    i_rst, '0)
`dff_cg_srst(reg,                              windowShape,        i_clk, wr_windowShape,        i_rst, '0)
`dff_cg_srst(reg [SAMPLE_RATE_NEGEXP_W-1:0],   sampleRateNegExp,   i_clk, wr_sampleRateNegExp,   i_rst, '0)
`dff_cg_srst(reg,                              sampleMode,         i_clk, wr_sampleMode,         i_rst, '0)
`dff_cg_srst(reg [SAMPLE_JITTER_NEGEXP_W-1:0], sampleJitterNegExp, i_clk, wr_sampleJitterNegExp, i_rst, '0)
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

always @*
  if (addrInRange)
    case (addr_q)
      '0:                            rdData_d = value0;

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
  else
    rdData_d = '0;

// Backpressure goes straight through so destination controls all flow, so the
// sink must keep accepting data.
assign o_bp_ready = i_bp_ready && !inBurstRd;

assign o_bp_data = rdData_q;
assign o_bp_valid = rd_q;

endmodule
