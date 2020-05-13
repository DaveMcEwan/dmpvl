`include "dff.vh"

module xoroshiro #(
  parameter WINLEN = 256, // Must be power-of-2, at least 4, or 0 for no window.
  parameter WINPERIODIC = 0, // 0->Time randomly sampled, 1->Time from wrapping counter.
  parameter ALGORITHM = 1, // 0->Dummy, for baseline logic measurement only.
                           // 1->Xoroshiro128+
                           // 2->Xoshiro128++
                           // 3->Xoshiro128+
                           // 4->Xoshiro256+
                           // 5->Xoroshiro64*
  parameter WR_ACK_NOT_PREV = 1 // Writes return 0->ACK/unknown value, 1->previous value.
) (
  input wire          i_clk,
  input wire          i_rst,
  input wire          i_cg,

  input  wire [7:0]   i_bp_data,
  input  wire         i_bp_valid,
  output wire         o_bp_ready,

  output wire [7:0]   o_bp_data,
  output wire         o_bp_valid,
  input  wire         i_bp_ready
);

`dff_cg_srst(reg, wr, i_clk, i_cg, i_rst, '0) // 1b FSM
`dff_cg_srst(reg, rd, i_clk, i_cg, i_rst, '0) // 1b FSM
`dff_cg_norst(reg [6:0], addr, i_clk, i_cg)
`dff_cg_srst(reg [7:0], burst, i_clk, i_cg, i_rst, '0) // 8b downcounter

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

wire memory_updt;
generate if (WR_ACK_NOT_PREV != 0) begin
  // The returned value for on writes is not necessarily the previous value
  // since memory is updated in preparation for accepting.
  // Relies on data being held steady while valid is high but ready is low.
  assign memory_updt = i_cg && wr_q && i_bp_valid; // Faster, less logic.
end else begin
  assign memory_updt = i_cg && doWrite;
end endgenerate

wire rdData_updt =
  (!wr_q && i_bp_valid) ||    // Single Read initiated
  rd_q ||                     // Burst Read in-progress
  wr_q;                       // End of Write

// The only writable thing is the 128b seed.
wire seedValid = memory_updt && addr_q[0]; // @1
wire [127:0] s1s0_wr = {s1[55:0],  s0,  i_bp_data};
wire [63:0] seedS0 = s1s0_wr[0 +: 64];
wire [63:0] seedS1 = s1s0_wr[64 +: 64];

wire [63:0] s0, s1, prngResult;
generate if (ALGORITHM == 1) begin
  prngXoroshiro128p u_prng (
    .i_clk              (i_clk),
    .i_rst              (i_rst),
    .i_cg               (i_cg),

    .i_seedValid        (seedValid),
    .i_seedS0           (seedS0),
    .i_seedS1           (seedS1),

    .o_s0               (s0),
    .o_s1               (s1),
    .o_result           (prngResult)
  );
end else if (ALGORITHM == 2) begin
  prngXoshiro128pp u_prng (
    .i_clk              (i_clk),
    .i_rst              (i_rst),
    .i_cg               (i_cg),

    .i_seedValid        (seedValid),
    .i_seedS0           (seedS0[31:0]),
    .i_seedS1           (seedS0[63:32]),
    .i_seedS2           (seedS1[31:0]),
    .i_seedS3           (seedS1[63:32]),

    .o_s0               (s0[31:0]),
    .o_s1               (s0[63:32]),
    .o_s2               (s1[31:0]),
    .o_s3               (s1[63:32]),
    .o_result           (prngResult[31:0])
  );
  // Repeat 32b outputs to make 64b results compatible with reading upper byte.
  assign prngResult[63:32] = prngResult[31:0];
end else if (ALGORITHM == 3) begin
  prngXoshiro128p u_prng (
    .i_clk              (i_clk),
    .i_rst              (i_rst),
    .i_cg               (i_cg),

    .i_seedValid        (seedValid),
    .i_seedS0           (seedS0[31:0]),
    .i_seedS1           (seedS0[63:32]),
    .i_seedS2           (seedS1[31:0]),
    .i_seedS3           (seedS1[63:32]),

    .o_s0               (s0[31:0]),
    .o_s1               (s0[63:32]),
    .o_s2               (s1[31:0]),
    .o_s3               (s1[63:32]),
    .o_result           (prngResult[31:0])
  );
  // Repeat 32b outputs to make 64b results compatible with reading upper byte.
  assign prngResult[63:32] = prngResult[31:0];
end else if (ALGORITHM == 4) begin
  wire [63:0] s2, s3;
  wire [127:0] s3s2_wr = {s3[55:0],  s2,  s1[63:56]};
  wire [63:0] seedS2 = s3s2_wr[0 +: 64];
  wire [63:0] seedS3 = s3s2_wr[64 +: 64];
  prngXoshiro256p u_prng (
    .i_clk              (i_clk),
    .i_rst              (i_rst),
    .i_cg               (i_cg),

    .i_seedValid        (seedValid),
    .i_seedS0           (seedS0),
    .i_seedS1           (seedS1),
    .i_seedS2           (seedS2),
    .i_seedS3           (seedS3),

    .o_s0               (s0),
    .o_s1               (s1),
    .o_s2               (s2),
    .o_s3               (s3),
    .o_result           (prngResult)
  );
end else if (ALGORITHM == 5) begin
  prngXoroshiro64s u_prng (
    .i_clk              (i_clk),
    .i_rst              (i_rst),
    .i_cg               (i_cg),

    .i_seedValid        (seedValid),
    .i_seedS0           (seedS0[31:0]),
    .i_seedS1           (seedS1[31:0]),

    .o_s0               (s0[31:0]),
    .o_s1               (s1[31:0]),
    .o_result           (prngResult[31:0])
  );
  // Repeat 32b outputs to make 64b results compatible with shifting to
  // initialize seed, and reading upper byte.
  assign s0[63:32] = s0[31:0];
  assign s1[63:32] = s1[31:0];
  assign prngResult[63:32] = prngResult[31:0];
end else begin
  // Dummy option for getting a baseline number for resource requirements.
  assign s0 = 64'h1234567812345678;
  assign s1 = 64'h8765432187654321;
  assign prngResult = 64'h55aa55aa55aa55aa;
end endgenerate
wire [7:0] prngResultByte7 = prngResult[8*7 +: 8];
wire [7:0] prngResultByte6 = prngResult[8*6 +: 8];
wire [7:0] prngResultByte5 = prngResult[8*5 +: 8];
wire [7:0] prngResultByte4 = prngResult[8*4 +: 8];
wire [7:0] prngResultByte3 = prngResult[8*3 +: 8];
wire [7:0] prngResultByte2 = prngResult[8*2 +: 8];
wire [7:0] prngResultByte1 = prngResult[8*1 +: 8];
wire [7:0] prngResultByte0 = prngResult[8*0 +: 8];

wire [127:0] s1s0_rd = {s1, s0};
wire [7:0] stateByte = s1s0_rd[8*addr_q[3:0] +: 8]; // @16..31

/*
Vigna and Blackman note that the lower bits fail linearity tests.

    We suggest to use a sign test to extract a random Boolean value, and
    right shifts to extract subsets of bits.

Data is generated much faster than can be read over USB at 64b per cycle at
48MHz (3.072 Gb/s) so only the upper byte of the result is readable.

Where WINLEN is non-zero a windowing function "logdrop" is applied.
*/
wire [7:0] resultByte;
generate if (WINLEN != 0) begin
  localparam WINLEN_W = $clog2(WINLEN);

  wire [WINLEN_W-1:0] winIdx;
  if (WINPERIODIC != 0) begin
    `dff_upcounter(reg [WINLEN_W-1:0], t, i_clk, i_cg, i_rst)
    assign winIdx = t_q;
  end else begin
    assign winIdx = prngResultByte6;
  end

  logdropWindow #(
    .DATA_W         (8),
    .WINLEN         (WINLEN),
    .ABSTRACT_MODEL (0)
  ) u_win (
    .i_t  (winIdx),
    .i_x  (prngResultByte7),
    .o_y  (resultByte)
  );
end else begin
  assign resultByte = prngResultByte7;
end endgenerate

`dff_cg_norst(reg [7:0], rdData, i_clk, i_cg && rdData_updt)
always @* rdData_d = addr_q[4] ? stateByte :
                                ((addr_q == '0) ? '0 : resultByte);

// Backpressure goes straight through so destination controls all flow, so the
// sink must keep accepting data.
assign o_bp_ready = i_bp_ready && !inBurstRd;

assign o_bp_data = rdData_q;
assign o_bp_valid = rd_q;

endmodule
