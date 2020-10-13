`include "dff.svh"

/* BytePipe interface, indended to sit on top of USB for register access.
Unpack the register map to wires.
*/
module bpReg #(
  parameter N_PROBE               = 4, // 2..64
  parameter N_PAIR                = 2, // 1..8
  parameter MAX_WINDOW_LENGTH_EXP = 32,
  parameter MAX_SAMPLE_PERIOD_EXP = 32,
  parameter MAX_SAMPLE_JITTER_EXP = 32,
  parameter WINDOW_PRECISION      = 32, // >= MAX_WINDOW_LENGTH_EXP
  parameter PKTFIFO_DEPTH         = 10  // Bytes, not packets.
) (
  input wire          i_clk,
  input wire          i_rst,
  input wire          i_cg,

  input  wire [N_PAIR*8-1:0]  i_pktfifo_data,
  input  wire [N_PAIR-1:0]    i_pktfifo_empty, // !valid
  output wire [N_PAIR-1:0]    o_pktfifo_pop, // ready
  output wire [N_PAIR-1:0]    o_pktfifo_flush,

  output wire [N_PAIR*$clog2(MAX_WINDOW_LENGTH_EXP+1)-1:0]  o_reg_windowLengthExp,
  output wire [N_PAIR-1:0]                                  o_reg_windowShape,
  output wire [N_PAIR*$clog2(MAX_SAMPLE_PERIOD_EXP+1)-1:0]  o_reg_samplePeriodExp,
  output wire [N_PAIR*$clog2(MAX_SAMPLE_JITTER_EXP+1)-1:0]  o_reg_sampleJitterExp,
  output wire [N_PAIR*3-1:0]                                o_reg_ledSource,
  output wire [N_PAIR*$clog2(N_PROBE)-1:0]                  o_reg_xSource,
  output wire [N_PAIR*$clog2(N_PROBE)-1:0]                  o_reg_ySource,

  output wire [N_PAIR*8-1:0]  o_jitterSeedByte,
  output wire [N_PAIR-1:0]    o_jitterSeedValid,

  input  wire [8-1:0] i_bp_data,
  input  wire         i_bp_valid,
  output wire         o_bp_ready,

  output wire [8-1:0] o_bp_data,
  output wire         o_bp_valid,
  input  wire         i_bp_ready
);

genvar i;

// Address for all regs per pair.
localparam STRIDE_PER_PAIR = 16;
localparam ADDR_REG_HI = N_PAIR*STRIDE_PER_PAIR - 1;
// 0th address of each pair is an alias to BytePipe burst@0.
localparam ADDR_PKTFIFO_RD                = 1;  // Rfifo
localparam ADDR_PKTFIFO_FLUSH             = 2;  // WO
localparam ADDR_PRNG_SEED                 = 3;  // WO
localparam ADDR_PKTFIFO_DEPTH             = 4;  // RO
localparam ADDR_MAX_WINDOW_LENGTH_EXP     = 5;  // RO
localparam ADDR_LOGDROP_PRECISION         = 6;  // RO
localparam ADDR_MAX_SAMPLE_PERIOD_EXP     = 7;  // RO
localparam ADDR_MAX_SAMPLE_JITTER_EXP     = 8;  // RO
localparam ADDR_WINDOW_LENGTH_EXP         = 9;  // RW
localparam ADDR_WINDOW_SHAPE              = 10; // RW
localparam ADDR_SAMPLE_PERIOD_EXP         = 11; // RW
localparam ADDR_SAMPLE_JITTER_EXP         = 12; // RW
localparam ADDR_LED_SOURCE                = 13; // RW
localparam ADDR_X_SOURCE                  = 14; // RW
localparam ADDR_Y_SOURCE                  = 15; // RW

localparam ADDR_W = $clog2(ADDR_REG_HI); // Registers plus burst@0.

`dff_cg_srst(reg, wr, i_clk, i_cg, i_rst, '0) // 1b FSM
`dff_cg_srst(reg, rd, i_clk, i_cg, i_rst, '0) // 1b FSM
`dff_cg_norst(reg [6:0], addr, i_clk, i_cg)
`dff_cg_srst(reg [7:0], burst, i_clk, i_cg, i_rst, '0) // 8b downcounter

wire [ADDR_W-1:0] rdAddr = addr_q[ADDR_W-1:0];
wire [3:0] addrReg = addr_q[3:0];
wire [2:0] addrPair = addr_q[6:4];
wire addrInRange = (ADDR_REG_HI[6:4] >= addrPair);

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
wire [N_PAIR-1:0] doWriteReg;
wire [N_PAIR-1:0] wr_windowLengthExp;
wire [N_PAIR-1:0] wr_windowShape;
wire [N_PAIR-1:0] wr_samplePeriodExp;
wire [N_PAIR-1:0] wr_sampleJitterExp;
wire [N_PAIR-1:0] wr_ledSource;
wire [N_PAIR-1:0] wr_xSource;
wire [N_PAIR-1:0] wr_ySource;

generate for (i = 0; i < N_PAIR; i=i+1) begin
  assign doWriteReg[i] = i_cg && doWrite && (addrPair == i);

  assign wr_windowLengthExp[i]  = doWriteReg[i] && (addrReg == ADDR_WINDOW_LENGTH_EXP);
  assign wr_windowShape[i]      = doWriteReg[i] && (addrReg == ADDR_WINDOW_SHAPE);
  assign wr_samplePeriodExp[i]  = doWriteReg[i] && (addrReg == ADDR_SAMPLE_PERIOD_EXP);
  assign wr_sampleJitterExp[i]  = doWriteReg[i] && (addrReg == ADDR_SAMPLE_JITTER_EXP);
  assign wr_ledSource[i]        = doWriteReg[i] && (addrReg == ADDR_LED_SOURCE);
  assign wr_xSource[i]          = doWriteReg[i] && (addrReg == ADDR_X_SOURCE);
  assign wr_ySource[i]          = doWriteReg[i] && (addrReg == ADDR_Y_SOURCE);

  assign o_jitterSeedByte[i*8 +: 8] = i_bp_data;
  assign o_jitterSeedValid[i]       = doWriteReg[i] && (addrReg == ADDR_PRNG_SEED);
end endgenerate


// Widths and value enumerations.
localparam WINDOW_LENGTH_EXP_W      = $clog2(MAX_WINDOW_LENGTH_EXP+1);
localparam WINDOW_SHAPE_RECTANGULAR = 1'd0;
localparam WINDOW_SHAPE_LOGDROP     = 1'd1;
localparam SAMPLE_PERIOD_EXP_W      = $clog2(MAX_SAMPLE_PERIOD_EXP+1);
localparam SAMPLE_JITTER_EXP_W      = $clog2(MAX_SAMPLE_JITTER_EXP+1);
localparam PROBE_SELECT_W           = $clog2(N_PROBE);
localparam LED_SOURCE_W             = 3;

`dff_nocg_srst(reg [N_PAIR*WINDOW_LENGTH_EXP_W-1:0], windowLengthExp, i_clk, i_rst, '0)
`dff_nocg_srst(reg [N_PAIR-1:0],                     windowShape,     i_clk, i_rst, '0)
`dff_nocg_srst(reg [N_PAIR*SAMPLE_PERIOD_EXP_W-1:0], samplePeriodExp, i_clk, i_rst, '0)
`dff_nocg_srst(reg [N_PAIR*SAMPLE_JITTER_EXP_W-1:0], sampleJitterExp, i_clk, i_rst, '0)
`dff_nocg_srst(reg [N_PAIR*LED_SOURCE_W-1:0],        ledSource,       i_clk, i_rst, '0)
`dff_nocg_srst(reg [N_PAIR*PROBE_SELECT_W-1:0],      xSource,         i_clk, i_rst, '0)
`dff_nocg_srst(reg [N_PAIR*PROBE_SELECT_W-1:0],      ySource,         i_clk, i_rst, '0)
generate for (i = 0; i < N_PAIR; i=i+1) begin
  always @* windowLengthExp_d[i*WINDOW_LENGTH_EXP_W +: WINDOW_LENGTH_EXP_W] =
    wr_windowLengthExp[i] ?
    i_bp_data[WINDOW_LENGTH_EXP_W-1:0] :
    windowLengthExp_q[i*WINDOW_LENGTH_EXP_W +: WINDOW_LENGTH_EXP_W];

  always @* windowShape_d[i] =
    wr_windowShape[i] ?
    i_bp_data[0] :
    windowShape_q[i];

  always @* samplePeriodExp_d[i*SAMPLE_PERIOD_EXP_W +: SAMPLE_PERIOD_EXP_W] =
    wr_samplePeriodExp[i] ?
    i_bp_data[SAMPLE_PERIOD_EXP_W-1:0] :
    samplePeriodExp_q[i*SAMPLE_PERIOD_EXP_W +: SAMPLE_PERIOD_EXP_W];

  always @* sampleJitterExp_d[i*SAMPLE_JITTER_EXP_W +: SAMPLE_JITTER_EXP_W] =
    wr_sampleJitterExp[i] ?
    i_bp_data[SAMPLE_JITTER_EXP_W-1:0] :
    sampleJitterExp_q[i*SAMPLE_JITTER_EXP_W +: SAMPLE_JITTER_EXP_W];

  always @* ledSource_d[i*LED_SOURCE_W +: LED_SOURCE_W] =
    wr_ledSource[i] ?
    i_bp_data[LED_SOURCE_W-1:0] :
    ledSource_q[i*LED_SOURCE_W +: LED_SOURCE_W];

  always @* xSource_d[i*PROBE_SELECT_W +: PROBE_SELECT_W] =
    wr_xSource[i] ?
    i_bp_data[PROBE_SELECT_W-1:0] :
    xSource_q[i*PROBE_SELECT_W +: PROBE_SELECT_W];

  always @* ySource_d[i*PROBE_SELECT_W +: PROBE_SELECT_W] =
    wr_ySource[i] ?
    i_bp_data[PROBE_SELECT_W-1:0] :
    ySource_q[i*PROBE_SELECT_W +: PROBE_SELECT_W];
end endgenerate

// Expose non-static (RW) regs as wires.
assign o_reg_windowLengthExp = windowLengthExp_q;
assign o_reg_windowShape     = windowShape_q;
assign o_reg_samplePeriodExp = samplePeriodExp_q;
assign o_reg_sampleJitterExp = sampleJitterExp_q;
assign o_reg_ledSource       = ledSource_q;
assign o_reg_xSource         = xSource_q;
assign o_reg_ySource         = ySource_q;

`dff_cg_norst(reg [7:0], rdData, i_clk, i_cg && rd_d)
always @*
  if (addrInRange)
    case (addrReg)
      ADDR_PKTFIFO_RD:              rdData_d = i_pktfifo_data[addrPair*8 +: 8];

      // RO static
      ADDR_PKTFIFO_DEPTH:           rdData_d = PKTFIFO_DEPTH;
      ADDR_MAX_WINDOW_LENGTH_EXP:   rdData_d = MAX_WINDOW_LENGTH_EXP;
      ADDR_LOGDROP_PRECISION:       rdData_d = WINDOW_PRECISION;
      ADDR_MAX_SAMPLE_PERIOD_EXP:   rdData_d = MAX_SAMPLE_PERIOD_EXP;
      ADDR_MAX_SAMPLE_JITTER_EXP:   rdData_d = MAX_SAMPLE_JITTER_EXP;
                                                  /* verilator lint_off WIDTH */
      // RW
      ADDR_WINDOW_LENGTH_EXP:       rdData_d = windowLengthExp_q[addrPair*WINDOW_LENGTH_EXP_W +: WINDOW_LENGTH_EXP_W];
      ADDR_WINDOW_SHAPE:            rdData_d = windowShape_q[addrPair];
      ADDR_SAMPLE_PERIOD_EXP:       rdData_d = samplePeriodExp_q[addrPair*SAMPLE_PERIOD_EXP_W +: SAMPLE_PERIOD_EXP_W];
      ADDR_SAMPLE_JITTER_EXP:       rdData_d = sampleJitterExp_q[addrPair*SAMPLE_JITTER_EXP_W +: SAMPLE_JITTER_EXP_W];
      ADDR_LED_SOURCE:              rdData_d = ledSource_q[addrPair*LED_SOURCE_W +: LED_SOURCE_W];
      ADDR_X_SOURCE:                rdData_d = xSource_q[addrPair*PROBE_SELECT_W +: PROBE_SELECT_W];
      ADDR_Y_SOURCE:                rdData_d = ySource_q[addrPair*PROBE_SELECT_W +: PROBE_SELECT_W];
                                                  /* verilator lint_on  WIDTH */
      default:                      rdData_d = '0;
    endcase
  else
    rdData_d = '0;

generate for (i = 0; i < N_PAIR; i=i+1) begin
  assign o_pktfifo_pop[i] = rd_q && (addrReg == ADDR_PKTFIFO_RD) && (addrPair == i);
  assign o_pktfifo_flush[i] = doWriteReg[i] && (addrReg == ADDR_PKTFIFO_FLUSH);
end endgenerate

// Read data is always valid, except reading an empty fifo.
`dff_cg_srst(reg, rdValid, i_clk, i_cg && rd_d, i_rst, 1'b0)
always @*
  if (addrInRange)
    case (addrReg)
                                                  /* verilator lint_off WIDTH */
      ADDR_PKTFIFO_RD: rdValid_d = !i_pktfifo_empty[addrPair];
                                                  /* verilator lint_on  WIDTH */
      default:         rdValid_d = 1'b1;
    endcase
  else
    rdValid_d = 1'b1;

// Backpressure goes straight through so destination controls all flow, so the
// sink must keep accepting data.
wire pktfifo_popEmpty = |(o_pktfifo_pop & i_pktfifo_empty);
assign o_bp_ready = i_bp_ready && !inBurstRd && !pktfifo_popEmpty;

assign o_bp_data = rdData_q;
assign o_bp_valid = rd_q && rdValid_q;

endmodule
