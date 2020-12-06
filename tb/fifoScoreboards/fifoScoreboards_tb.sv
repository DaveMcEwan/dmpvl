`include "dff.svh"
`include "misc.svh"

/** fifoScoreboards_tb
 * Instance single fifo-like design with
 */
module fifoScoreboards_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire           i_clk,
  input  wire           i_rst
`endif
);

// Convert -Ddefines into localparams to keep preprocessor behaviour in single
// place for good linting.
localparam string DUT_TYPE    = `STRING(`DUT_TYPE);
localparam WIDTH              = `WIDTH;
localparam DEPTH              = `DEPTH;
localparam FLOPS_NOT_MEM      = `FLOPS_NOT_MEM;
localparam TOPOLOGY           = `TOPOLOGY;
localparam CDC                = `CDC;

// N_CYCLES is the number of tbclk cycles to randomize inputs to DUT.
// As data may take some time to get through a FIFO, N_OUTFLOW is the number of
// tbclk cycles to allow data to flow out of FIFOs.
// Since clockgates are randomized and clocks run at random ratios, it is not
// guaranteed that the DUT will be emptied ever, but a big enough number for
// N_OUTFLOW makes it highly likely.
localparam N_CYCLES = `N_CYCLES;
localparam N_OUTFLOW = 1000;

// {{{ clock,clockgate,reset,dump

wire tbclk, wclk, rclk;
generateClock u_tbclk (
`ifdef VERILATOR // V_erilator must drive its own root clock
  .i_rootClk        (i_clk),
`endif
  .o_clk            (tbclk),
  .i_periodHi       (8'd0),
  .i_periodLo       (8'd0),
  .i_jitterControl  (8'd0)
);

generate if (CDC) begin
  localparam CLKPERIOD_CTRL_A = 3; // ?clk between 1/1 and 1/8 rate of tbclk.
  localparam CLKPERIOD_CTRL_B = 15; // Change ?clk after approx 32k cycles.
  localparam CLKPERIOD_CTRL_MASK = (1 << CLKPERIOD_CTRL_A) - 1;
  localparam CLKPERIOD_CTRL_MOD = (1 << CLKPERIOD_CTRL_B);
  reg [31:0] wclkCtrlPeriod, rclkCtrlPeriod;

  initial begin
    wclkCtrlPeriod = 5;
    rclkCtrlPeriod = 5;
  end
  always @(posedge tbclk) begin
    if ($random % CLKPERIOD_CTRL_MOD == 0) wclkCtrlPeriod <= $random & CLKPERIOD_CTRL_MASK;
    if ($random % CLKPERIOD_CTRL_MOD == 0) rclkCtrlPeriod <= $random & CLKPERIOD_CTRL_MASK;
  end

  strobe #(
    .CTRL_PERIOD_W    (CLKPERIOD_CTRL_A),
    .CTRL_JITTER_W    (1),
    .N_STROBE         (1),
    .ENABLE_JITTER    (0)
  ) u_wclk (
    .i_clk              (tbclk),
    .i_rst              (1'b0),
    .i_cg               (1'b1),

    .i_ctrlPeriodM1     (wclkCtrlPeriod[CLKPERIOD_CTRL_A-1:0]),
    .i_ctrlJitter       ('0),

    .i_jitterSeedByte   ('0),
    .i_jitterSeedValid  (1'b0),
    .o_jitterPrng       (),

    .o_strobe           (wclk)
  );

  strobe #(
    .CTRL_PERIOD_W    (CLKPERIOD_CTRL_A),
    .CTRL_JITTER_W    (1),
    .N_STROBE         (1),
    .ENABLE_JITTER    (0)
  ) u_rclk (
    .i_clk              (tbclk),
    .i_rst              (1'b0),
    .i_cg               (1'b1),

    .i_ctrlPeriodM1     (rclkCtrlPeriod[CLKPERIOD_CTRL_A-1:0]),
    .i_ctrlJitter       ('0),

    .i_jitterSeedByte   ('0),
    .i_jitterSeedValid  (1'b0),
    .o_jitterPrng       (),

    .o_strobe           (rclk)
  );
end else begin
  assign wclk = tbclk;
  assign rclk = tbclk;
end endgenerate

`dff_nocg_norst(reg [31:0], nCycles, tbclk)
initial nCycles_q = '0;
always @* nCycles_d = nCycles_q + 'd1;

wire outflowStage = (nCycles_q > N_CYCLES);

reg rst;
wire wrst = rst;
wire rrst = rst;

`ifdef VERILATOR // V_erilator tb drives its own clockgate,reset
always @* rst = i_rst;
`else
initial rst = 1'b1;
always @* rst = (nCycles_q <= 20);

initial begin
  $dumpfile("fifoScoreboards_tb.iverilog.vcd");
  $dumpvars(0, fifoScoreboards_tb);
end
`endif

// Clockgates drop between 1/20 and 1/(CGRATE_CTRL_C * 2**CGRATE_CTRL_A).
// Rates changes around every 2**CGRATE_CTRL_B cycles.
// ==> Clockgates drop between 1/20 and 1/640 cycles, with actual rate changing
//     roughly every 64ki cycles.
localparam CGRATE_CTRL_A = 5;
localparam CGRATE_CTRL_B = 16;
localparam CGRATE_CTRL_C = 20;
localparam CGRATE_CTRL_MASK = (1 << CGRATE_CTRL_A) - 1;
localparam CGRATE_CTRL_MOD = (1 << CGRATE_CTRL_B);
reg [31:0] wcgRate, rcgRate;
initial begin
  wcgRate = 5;
  rcgRate = 5;
end
always @(posedge tbclk) begin
  if ($random % CGRATE_CTRL_MOD == 0) wcgRate <= $random & CGRATE_CTRL_MASK;
  if ($random % CGRATE_CTRL_MOD == 0) rcgRate <= $random & CGRATE_CTRL_MASK;
end

reg wcg, rcg;
always @(posedge tbclk) wcg <= ($random % ((wcgRate+'d1) * CGRATE_CTRL_C)) != 0;

generate if (CDC) begin
  always @(posedge tbclk) rcg <= ($random % ((rcgRate+'d1) * CGRATE_CTRL_C)) != 0;
end else begin
  always @* rcg = wcg;
end endgenerate

// }}} clock,clockgate,reset,dump

// {{{ Randomized inputs

// Handshake/flow-controls pulse between 1/1 and 1/2**FLOWRATE_CTRL_A.
// Rates changes around every 2**FLOWRATE_CTRL_B cycles.
// ==> Flow-controls pulse between 1/1 and 1/8 cycles, with actual rate changing
//     roughly every 512 cycles.
localparam FLOWRATE_CTRL_A = 3;
localparam FLOWRATE_CTRL_B = 9;
localparam FLOWRATE_CTRL_MASK = (1 << FLOWRATE_CTRL_A) - 1;
localparam FLOWRATE_CTRL_MOD = (1 << FLOWRATE_CTRL_B);
reg [31:0] wvalidRate, rreadyRate;
initial begin
  wvalidRate = 5;
  rreadyRate = 5;
end
always @(posedge tbclk) begin
  if ($random % FLOWRATE_CTRL_MOD == 0) wvalidRate <= $random & FLOWRATE_CTRL_MASK;
  if ($random % FLOWRATE_CTRL_MOD == 0) rreadyRate <= $random & FLOWRATE_CTRL_MASK;
end

reg [31:0] wdata32;
reg wvalid, rready;
wire [WIDTH-1:0] wdata = wdata32[WIDTH-1:0];
always @(posedge tbclk)
  if (outflowStage) begin
    wdata32  <= '0;
    wvalid   <= 1'b0;
    rready   <= 1'b1;
  end else begin
    wdata32  <= $random;
    wvalid   <= ($random % (wvalidRate+'d1)) == 0;
    rready   <= ($random % (rreadyRate+'d1)) == 0;
  end

// }}} Randomized inputs

// {{{ Record pushed and popped data
wire pushed = wcg && wvalid && wready;
wire popped = rcg && rvalid && rready;
integer fPushed, fPopped;
initial begin
  fPushed = $fopen("pushed.log", "w");
  fPopped = $fopen("popped.log", "w");

  $fwrite(fPushed, "nCycles_q wdata\n");
  $fwrite(fPopped, "nCycles_q rdata\n");
end

always @(posedge wclk) if (pushed) $fwrite(fPushed, "%0d %0h\n", nCycles_q, wdata);
always @(posedge rclk) if (popped) $fwrite(fPopped, "%0d %0h\n", nCycles_q, rdata);

// Finish sim after an upper limit on the number of clock cycles.
always @* if (nCycles_q > (N_CYCLES+N_OUTFLOW)) begin
  $fclose(fPushed);
  $fclose(fPopped);
  $finish;
end
// }}} Record pushed and popped data

wire wready;
wire [WIDTH-1:0] rdata;
wire rvalid;

generate if (DUT_TYPE == "fifoW1R1") begin // {{{ DUT
  fifoW1R1 #(
    .WIDTH              (WIDTH),
    .DEPTH              (DEPTH),
    .FLOPS_NOT_MEM      (FLOPS_NOT_MEM),
    .FORCEKEEP_NENTRIES (0)
  ) u_dut (
    // NOTE: Single clock domain could use either wclk or rclk;
    .i_clk      (wclk),
    .i_rst      (wrst),
    .i_cg       (wcg),

    .i_flush    (1'b0),

    .i_data     (wdata),
    .i_valid    (wvalid),
    .o_ready    (wready),

    .o_data     (rdata),
    .o_valid    (rvalid),
    .i_ready    (rready),

    .o_pushed   (),
    .o_popped   (),

    .o_wptr     (),
    .o_rptr     (),

    .o_validEntries (),
    .o_nEntries     (),

    .o_entries  ()
  );
end else if (DUT_TYPE == "cdcData") begin
  cdcData #(
    .WIDTH          (WIDTH),
    .TOPOLOGY       (TOPOLOGY),
    .FLOPS_NOT_MEM  (FLOPS_NOT_MEM)
  ) u_dut (
    .i_wclk     (wclk),
    .i_wrst     (wrst),
    .i_wcg      (wcg),

    .i_rclk     (rclk),
    .i_rrst     (rrst),
    .i_rcg      (rcg),

    .i_wdata    (wdata),
    .i_wvalid   (wvalid),
    .o_wready   (wready),

    .o_rdata    (rdata),
    .o_rvalid   (rvalid),
    .i_rready   (rready)
  );
end else if (DUT_TYPE == "cdcFifo") begin
  cdcFifo #(
    .WIDTH          (WIDTH),
    .DEPTH          (DEPTH),
    .FLOPS_NOT_MEM  (FLOPS_NOT_MEM),
    .TOPOLOGY       (TOPOLOGY)
  ) u_dut (
    .i_wclk     (wclk),
    .i_wrst     (wrst),
    .i_wcg      (wcg),

    .i_rclk     (rclk),
    .i_rrst     (rrst),
    .i_rcg      (rcg),

    .i_wdata    (wdata),
    .i_wvalid   (wvalid),
    .o_wready   (wready),

    .o_rdata    (rdata),
    .o_rvalid   (rvalid),
    .i_rready   (rready),

    .o_wptr     (),
    .o_rptr     (),

    .o_wpushed  (),
    .o_rpopped  ()
  );
end else initial begin
  $display("ERROR: Unsupported DUT_TYPE: %s", DUT_TYPE);
  $finish;
end endgenerate // }}} DUT

endmodule
