`include "dff.vh"

/* BytePipe interface, indended to sit on top of USB for register access.
Unpack the register map to wires.
*/
module bpReg #(
  parameter PKTFIFO_DEPTH         = 10, // packets
  parameter MAX_WINDOW_LENGTH_EXP = 32,
  parameter LOGDROP_PRECISION     = 32, // >= MAX_WINDOW_LENGTH_EXP
  parameter MAX_SAMPLE_PERIOD_EXP = 32,
  parameter MAX_SAMPLE_JITTER_EXP = 32
) (
  input wire          i_clk,
  input wire          i_rst,
  input wire          i_cg,

  input  wire [7:0]   i_pktfifo_data,
  input  wire         i_pktfifo_empty, // !valid
  output wire         o_pktfifo_pop, // ready
  output wire         o_pktfifo_flush,

  output wire [$clog2(MAX_WINDOW_LENGTH_EXP+1)-1:0]   o_reg_windowLengthExp,
  output wire                                         o_reg_windowShape,
  output wire [$clog2(MAX_SAMPLE_PERIOD_EXP+1)-1:0]   o_reg_samplePeriodExp,
  output wire [$clog2(MAX_SAMPLE_JITTER_EXP+1)-1:0]   o_reg_sampleJitterExp,

  output wire [7:0]   o_jitterSeedByte,
  output wire         o_jitterSeedValid,

  input  wire [7:0]   i_bp_data,
  input  wire         i_bp_valid,
  output wire         o_bp_ready,

  output wire [7:0]   o_bp_data,
  output wire         o_bp_valid,
  input  wire         i_bp_ready
);

// Address for all regs.
localparam N_REG = 12;
localparam ADDR_REG_LO = 1;
localparam ADDR_REG_HI = ADDR_REG_LO + N_REG - 1;
localparam ADDR_PKTFIFO_RD                = ADDR_REG_LO + 0;  // Rfifo
localparam ADDR_PKTFIFO_FLUSH             = ADDR_REG_LO + 1;  // WO
localparam ADDR_PRNG_SEED                 = ADDR_REG_LO + 2;  // WO
localparam ADDR_PKTFIFO_DEPTH             = ADDR_REG_LO + 3;  // RO
localparam ADDR_MAX_WINDOW_LENGTH_EXP     = ADDR_REG_LO + 4;  // RO
localparam ADDR_LOGDROP_PRECISION         = ADDR_REG_LO + 5;  // RO
localparam ADDR_MAX_SAMPLE_PERIOD_EXP     = ADDR_REG_LO + 6;  // RO
localparam ADDR_MAX_SAMPLE_JITTER_EXP     = ADDR_REG_LO + 7;  // RO
localparam ADDR_WINDOW_LENGTH_EXP         = ADDR_REG_LO + 8;  // RW
localparam ADDR_WINDOW_SHAPE              = ADDR_REG_LO + 9;  // RW
localparam ADDR_SAMPLE_PERIOD_EXP         = ADDR_REG_LO + 10; // RW
localparam ADDR_SAMPLE_JITTER_EXP         = ADDR_REG_LO + 11; // RW

localparam N_LOC = N_REG+1; // Registers plus burst@0.
localparam ADDR_W = $clog2(N_LOC);

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
wire wr_windowLengthExp = doWriteReg && (addr_q == ADDR_WINDOW_LENGTH_EXP);
wire wr_windowShape     = doWriteReg && (addr_q == ADDR_WINDOW_SHAPE);
wire wr_samplePeriodExp = doWriteReg && (addr_q == ADDR_SAMPLE_PERIOD_EXP);
wire wr_sampleJitterExp = doWriteReg && (addr_q == ADDR_SAMPLE_JITTER_EXP);

assign o_jitterSeedByte = i_bp_data;
assign o_jitterSeedValid = doWriteReg && (addr_q == ADDR_PRNG_SEED);

// Widths and value enumerations.
localparam WINDOW_LENGTH_EXP_W      = $clog2(MAX_WINDOW_LENGTH_EXP+1);
localparam WINDOW_SHAPE_RECTANGULAR = 1'd0;
localparam WINDOW_SHAPE_LOGDROP     = 1'd1;
localparam SAMPLE_PERIOD_EXP_W      = $clog2(MAX_SAMPLE_PERIOD_EXP+1);
localparam SAMPLE_JITTER_EXP_W      = $clog2(MAX_SAMPLE_JITTER_EXP+1);

`dff_cg_srst(reg [WINDOW_LENGTH_EXP_W-1:0], windowLengthExp, i_clk, wr_windowLengthExp, i_rst, '0)
`dff_cg_srst(reg,                           windowShape,     i_clk, wr_windowShape,     i_rst, '0)
`dff_cg_srst(reg [SAMPLE_PERIOD_EXP_W-1:0], samplePeriodExp, i_clk, wr_samplePeriodExp, i_rst, '0)
`dff_cg_srst(reg [SAMPLE_JITTER_EXP_W-1:0], sampleJitterExp, i_clk, wr_sampleJitterExp, i_rst, '0)
always @* windowLengthExp_d = i_bp_data[WINDOW_LENGTH_EXP_W-1:0];
always @* windowShape_d     = i_bp_data[0];
always @* samplePeriodExp_d = i_bp_data[SAMPLE_PERIOD_EXP_W-1:0];
always @* sampleJitterExp_d = i_bp_data[SAMPLE_JITTER_EXP_W-1:0];

// Expose non-static (RW) regs as wires.
assign o_reg_windowLengthExp = windowLengthExp_q;
assign o_reg_windowShape     = windowShape_q;
assign o_reg_samplePeriodExp = samplePeriodExp_q;
assign o_reg_sampleJitterExp = sampleJitterExp_q;

always @*
  if (addrInRange)
    case (addr_q)
      ADDR_PKTFIFO_RD:              rdData_d = i_pktfifo_data;

      // RO static
      ADDR_MAX_WINDOW_LENGTH_EXP:   rdData_d = MAX_WINDOW_LENGTH_EXP;
      ADDR_LOGDROP_PRECISION:       rdData_d = LOGDROP_PRECISION;
      ADDR_MAX_SAMPLE_PERIOD_EXP:   rdData_d = MAX_SAMPLE_PERIOD_EXP;
      ADDR_MAX_SAMPLE_JITTER_EXP:   rdData_d = MAX_SAMPLE_JITTER_EXP;
                                                  /* verilator lint_off WIDTH */
      // RW
      ADDR_WINDOW_LENGTH_EXP:       rdData_d = windowLengthExp_q;
      ADDR_WINDOW_SHAPE:            rdData_d = windowShape_q;
      ADDR_SAMPLE_PERIOD_EXP:       rdData_d = samplePeriodExp_q;
      ADDR_SAMPLE_JITTER_EXP:       rdData_d = sampleJitterExp_q;
                                                  /* verilator lint_on  WIDTH */
      default:                      rdData_d = '0;
    endcase
  else
    rdData_d = '0;

assign o_pktfifo_pop = rd_q && (addr_q == ADDR_PKTFIFO_RD);
assign o_pktfifo_flush = doWriteReg && (addr_q == ADDR_PKTFIFO_FLUSH);

// Read data is always ready, except if trying to read an empty fifo.
wire rdReady = !(o_pktfifo_pop && i_pktfifo_empty);

// Backpressure goes straight through so destination controls all flow, so the
// sink must keep accepting data.
assign o_bp_ready = i_bp_ready && !inBurstRd && rdReady;

assign o_bp_data = rdData_q;
assign o_bp_valid = rd_q && rdReady;

endmodule
