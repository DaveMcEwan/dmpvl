`include "dff.vh"

// Pseudo-Random Number Generator as designed by David Blackman and Sebastian
// Vigna, but in synthesizable Verilog.
// This module only implements the state storage and next().
// No jump() or long_jump() functionallity, but the seed control interface
// allows these to be implemented externally if required.
module prngXoshiro128pp  (
  input  wire                       i_clk,
  input  wire                       i_rst,
  input  wire                       i_cg,

  input  wire                       i_seedValid,
  input  wire [31:0]                i_seedS0,
  input  wire [31:0]                i_seedS1,
  input  wire [31:0]                i_seedS2,
  input  wire [31:0]                i_seedS3,
  output wire [31:0]                o_s0,
  output wire [31:0]                o_s1,
  output wire [31:0]                o_s2,
  output wire [31:0]                o_s3,

  output wire [31:0]                o_result
);

localparam a = 7;
localparam b = 9;
localparam c = 11;

/*
uint32_t next(void) {
  const uint32_t result = rotl(s[0] + s[3], 7) + s[0];

  const uint32_t t = s[1] << 9;

  s[2] ^= s[0];
  s[3] ^= s[1];
  s[1] ^= s[2];
  s[0] ^= s[3];

  s[2] ^= t;

  s[3] = rotl(s[3], 11);

  return result;
}
*/
wire [31:0] s0;
wire [31:0] s1;
wire [31:0] s2;
wire [31:0] s3;
`dff_cg_norst(reg [31:0], s0, i_clk, i_cg)
`dff_cg_norst(reg [31:0], s1, i_clk, i_cg)
`dff_cg_norst(reg [31:0], s2, i_clk, i_cg)
`dff_cg_norst(reg [31:0], s3, i_clk, i_cg)
`dff_cg_norst(reg [31:0], result, i_clk, i_cg)

// const uint32_t result = rotl(s[0] + s[3], 7) + s[0];
wire [31:0] s0p3 = s0_q + s3_q;
always @* result_d = {s0p3[31-a:0], s0p3[31:32-a]} + s0_q;

assign s2 = s2_q ^ s0_q; // s[2] ^= s[0];
assign s3 = s3_q ^ s1_q; // s[3] ^= s[1];
assign s1 = s1_q ^ s2_q; // s[1] ^= s[2];
assign s0 = s0_q ^ s3_q; // s[0] ^= s[3];

always @* s0_d = i_seedValid ? i_seedS0 : s0;
assign o_s0 = s0_q;

always @* s1_d = i_seedValid ? i_seedS1 : s1;
assign o_s1 = s1_q;

// const uint32_t t = s[1] << 9; ...; s[2] ^= t;
always @* s2_d = i_seedValid ? i_seedS2 : (s2 ^ (s1 << b));
assign o_s2 = s2_q;

// s[3] = rotl(s[3], 11);
always @* s3_d = i_seedValid ? i_seedS3 : {s3[31-c:0], s3[31:32-c]};
assign o_s3 = s3_q;

assign o_result = result_q;

endmodule
