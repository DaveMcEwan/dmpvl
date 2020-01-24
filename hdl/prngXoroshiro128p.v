`include "dff.vh"

// Pseudo-Random Number Generator as designed by David Blackman and Sebastian
// Vigna, but in synthesizable Verilog.
// This module only implements the state storage and next().
// No jump() or long_jump() functionallity, but the seed control interface
// allows these to be implemented externally if required.
module prngXoroshiro128p  (
  input  wire                       i_clk,
  input  wire                       i_rst,
  input  wire                       i_cg,

  input  wire                       i_seedValid,
  input  wire [63:0]                i_seedS0,
  input  wire [63:0]                i_seedS1,
  output wire [63:0]                o_s0,
  output wire [63:0]                o_s1,

  output wire [63:0]                o_result
);

// NOTE: 2018 values apparently give better results than 2016 version
// (a=55, b=14, c=36).
localparam a = 24;
localparam b = 16;
localparam c = 37;

/*
uint64_t next(void) {
  const uint64_t s0 = s[0];
  uint64_t s1 = s[1];
  const uint64_t result = s0 + s1;

  s1 ^= s0;
  s[0] = rotl(s0, 24) ^ s1 ^ (s1 << 16); // a, b
  s[1] = rotl(s1, 37); // c

  return result;
}
*/
wire [63:0] s0;
wire [63:0] s1;
`dff_cg_norst(reg [63:0], s0, i_clk, i_cg)
`dff_cg_norst(reg [63:0], s1, i_clk, i_cg)
`dff_cg_norst(reg [63:0], result, i_clk, i_cg)

always @* result_d = s0_q + s1_q;     // const uint64_t result = s0 + s1;

assign s0 = s0_q;                     // const uint64_t s0 = s[0];
assign s1 = s0_q ^ s1_q;              // uint64_t s1 = s[1]; s1 ^= s0;

always @*
  if (i_seedValid)
    s0_d = i_seedS0;
  else
    // s[0] = rotl(s0, 24) ^ s1 ^ (s1 << 16); // a, b
    s0_d =
      {s0[63-a:0], s0[63:64-a]} ^
      s1 ^
      (s1 << 16);
assign o_s0 = s0_q;

always @*
  if (i_seedValid)
    s1_d = i_seedS1;
  else
    // s[1] = rotl(s1, 37); // c
    s1_d = {s1[63-c:0], s1[63:64-c]};
assign o_s1 = s1_q;

assign o_result = result_q;

endmodule
