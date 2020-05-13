`include "dff.vh"

// Pseudo-Random Number Generator as designed by David Blackman and Sebastian
// Vigna, but in synthesizable Verilog.
// This module only implements the state storage and next().
// No jump() or long_jump() functionallity, but the seed control interface
// allows these to be implemented externally if required.
module prngXoshiro256p  (
  input  wire                       i_clk,
  input  wire                       i_rst,
  input  wire                       i_cg,

  input  wire                       i_seedValid,
  input  wire [63:0]                i_seedS0,
  input  wire [63:0]                i_seedS1,
  input  wire [63:0]                i_seedS2,
  input  wire [63:0]                i_seedS3,
  output wire [63:0]                o_s0,
  output wire [63:0]                o_s1,
  output wire [63:0]                o_s2,
  output wire [63:0]                o_s3,

  output wire [63:0]                o_result
);

localparam b = 17;
localparam c = 45;

/*
uint64_t next(void) {
  const uint64_t result = s[0] + s[3];

  const uint64_t t = s[1] << 17;

  s[2] ^= s[0];
  s[3] ^= s[1];
  s[1] ^= s[2];
  s[0] ^= s[3];

  s[2] ^= t;

  s[3] = rotl(s[3], 45);

  return result;
}
*/
wire [63:0] s0;
wire [63:0] s1;
wire [63:0] s2;
wire [63:0] s3;
`dff_cg_norst(reg [63:0], s0, i_clk, i_cg)
`dff_cg_norst(reg [63:0], s1, i_clk, i_cg)
`dff_cg_norst(reg [63:0], s2, i_clk, i_cg)
`dff_cg_norst(reg [63:0], s3, i_clk, i_cg)
`dff_cg_norst(reg [63:0], result, i_clk, i_cg)

// const uint64_t result = s[0] + s[3];
always @* result_d = s0_q + s3_q;

assign s2 = s2_q ^ s0_q; // s[2] ^= s[0];
assign s3 = s3_q ^ s1_q; // s[3] ^= s[1];
assign s1 = s1_q ^ s2_q; // s[1] ^= s[2];
assign s0 = s0_q ^ s3_q; // s[0] ^= s[3];

always @* s0_d = i_seedValid ? i_seedS0 : s0;
assign o_s0 = s0_q;

always @* s1_d = i_seedValid ? i_seedS1 : s1;
assign o_s1 = s1_q;

// const uint64_t t = s[1] << 17; ...; s[2] ^= t;
always @* s2_d = i_seedValid ? i_seedS2 : (s2 ^ (s1 << b));
assign o_s2 = s2_q;

// s[3] = rotl(s[3], 45);
always @* s3_d = i_seedValid ? i_seedS3 : {s3[63-c:0], s3[63:64-c]};
assign o_s3 = s3_q;

assign o_result = result_q;

endmodule
