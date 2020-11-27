`include "dff.svh"

// Generate a strobe by dividing clock.
// Optional jitter is Poisson distributed.
module strobe #(
  parameter CTRL_PERIOD_W = 16,
  parameter CTRL_JITTER_W = 8, // Must be <= 32
  parameter N_STROBE = 1, // N_STROBE*(CTRL_JITTER_W+1) <= 24
  parameter ENABLE_JITTER = 1
) (
  input  wire                       i_clk,
  input  wire                       i_rst,
  input  wire                       i_cg,

  input  wire [CTRL_PERIOD_W-1:0]   i_ctrlPeriodM1, // Period minus 1.
  input  wire [CTRL_JITTER_W-1:0]   i_ctrlJitter, // 0->NonJitter

  input  wire [7:0]                 i_jitterSeedByte,
  input  wire                       i_jitterSeedValid,
  output wire [31:0]                o_jitterPrng, // PRNG_RESULT_W

  output wire [N_STROBE-1:0]        o_strobe
);

genvar i;
genvar b;

wire [N_STROBE-1:0] extendNotShorten;
wire [N_STROBE-1:0] jitterThisCycle;

generate if (ENABLE_JITTER != '0) begin
  localparam PRNG_STATE_W = 128;
  localparam PRNG_RESULT_W = 32;
  wire [PRNG_STATE_W-1:0] prngState;
  wire [PRNG_STATE_W-1:0] prngSeed_wr = {prngState[PRNG_STATE_W-9:0], i_jitterSeedByte};
  prngXoshiro128p u_prngJitter (
    .i_clk              (i_clk),
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

  // Interleave compare and extendNotShorten bits to spread entropy as evenly
  // as possible between strobes.
  // - Strobe0 gets highest order bits, strobe1 gets next highest, etc.
  // - extendNotShorten comes from top bits
  // - compare comes from bits below extendNotShorten.
  for (i = 0; i < N_STROBE; i=i+1) begin
    /* Indices check/confirm with Python.
    N_STROBE = 2
    PRNG_RESULT_W = 32
    CTRL_JITTER_W = 8
    for i in range(N_STROBE):
        print("extendNotShorten", PRNG_RESULT_W - i - 1)
        print("compare", [PRNG_RESULT_W - N_STROBE*(CTRL_JITTER_W-b) - i - 1
                          for b in range(CTRL_JITTER_W)] )
    */

    wire [CTRL_JITTER_W-1:0] compare;
    for (b = 0; b < CTRL_JITTER_W; b=b+1) begin
      assign compare[b] = o_jitterPrng[PRNG_RESULT_W - N_STROBE*(CTRL_JITTER_W-b) - i - 1];
    end

    assign extendNotShorten[i] = o_jitterPrng[PRNG_RESULT_W - i - 1];

    // Only allow jitter when PRNG is running, otherwise the period will be
    // half because the comparison will always be true, but jitterShorten will
    // never assert.
    `dff_cg_norst_d(reg, prngRunning, i_clk, i_cg, (o_jitterPrng != '0))
    assign jitterThisCycle[i] = (compare < i_ctrlJitter) && prngRunning_q;
  end
end else begin
  assign o_jitterPrng = '0;
  assign jitterThisCycle = '0;
  assign extendNotShorten = '0;
end endgenerate

wire [N_STROBE-1:0] jitterExtend = jitterThisCycle & extendNotShorten;
wire [N_STROBE-1:0] jitterShorten = jitterThisCycle & ~extendNotShorten;

// Counters can change by these values:
// -0 <-- Extended period
// -1 <-- Exact period
// -2 <-- Shortened period
generate for (i = 0; i < N_STROBE; i=i+1) begin
  `dff_cg_norst(reg [CTRL_PERIOD_W-1:0], downCounter, i_clk, i_cg && !jitterExtend[i])
  always @*
    if (downCounter_q == '0)
      downCounter_d = i_ctrlPeriodM1;
    else if (jitterShorten[i] && (downCounter_q != 'd1))
      downCounter_d = downCounter_q - 'd2;
    else
      downCounter_d = downCounter_q - 'd1;

  // Pulse output high only when downcounter restarts.
  `dff_cg_srst(reg, strobe, i_clk, i_cg, i_rst, 1'b0)
  always @* strobe_d = (downCounter_q == '0) && !jitterExtend[i];
  assign o_strobe[i] = strobe_q;
end endgenerate

endmodule
