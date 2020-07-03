`include "dff.vh"

// Generate a strobe by dividing clock.
// Optional jitter is Poisson distributed.
module strobe #(
  parameter CTRL_PERIOD_W = 16,
  parameter CTRL_JITTER_W = 8, // Must be <= 32
  parameter ENABLE_JITTER = 1
) (
  input  wire                       i_clk,
  input  wire                       i_rst,
  input  wire                       i_cg,

  input  wire [CTRL_PERIOD_W-1:0]   i_ctrlPeriodM1, // Period minus 1.
  input  wire [CTRL_JITTER_W-1:0]   i_ctrlJitter, // 0->NonJitter

  input  wire [7:0]                 i_jitterSeedByte,
  input  wire                       i_jitterSeedValid,
  output wire [31:0]                o_jitterPrng,

  output wire                       o_strobe
);

wire jitterThisCycle;
generate if (ENABLE_JITTER != '0) begin
  wire [127:0] prngState;
  wire [127:0] prngSeed_wr = {prngState[127-8:0], i_jitterSeedByte};
  prngXoshiro128p u_prngJitter (
    .i_clk              (i_clk),
    .i_rst              (i_rst),
    .i_cg               (i_cg),

    .i_seedValid        (i_jitterSeedValid),
    .i_seedS0           (prngSeed_wr[31:0]),
    .i_seedS1           (prngSeed_wr[63:32]),
    .i_seedS2           (prngSeed_wr[95:64]),
    .i_seedS3           (prngSeed_wr[127:96]),

    .o_s0               (prngState[31:0]),
    .o_s1               (prngState[63:32]),
    .o_s2               (prngState[95:64]),
    .o_s3               (prngState[127:96]),
    .o_result           (o_jitterPrng)
  );

  wire [CTRL_JITTER_W-1:0] compare = o_jitterPrng[32-CTRL_JITTER_W +: CTRL_JITTER_W];
  assign jitterThisCycle = (compare < i_ctrlJitter);
end else begin
  assign o_jitterPrng = '0;
  assign jitterThisCycle = 1'b0;
end endgenerate

// -0 <-- Extended period
// -1 <-- Exact period
// -2 <-- Shortened period
wire extendNotShorten = o_jitterPrng[31-CTRL_JITTER_W];
wire jitterExtend = jitterThisCycle && extendNotShorten;
wire jitterShorten = jitterThisCycle && !extendNotShorten;
`dff_cg_norst(reg [CTRL_PERIOD_W-1:0], downCounter, i_clk, i_cg && !jitterExtend)
always @*
  if (downCounter_q == '0)
    downCounter_d = i_ctrlPeriodM1;
  else if (jitterShorten && (downCounter_q != 'd1))
    downCounter_d = downCounter_q - 'd2;
  else
    downCounter_d = downCounter_q - 'd1;

// Pulse output high only when downcounter restarts.
`dff_cg_srst(reg, strobe, i_clk, i_cg, i_rst, 1'b0)
always @* strobe_d = (downCounter_q == '0) && !jitterExtend;
assign o_strobe = strobe_q;

endmodule
