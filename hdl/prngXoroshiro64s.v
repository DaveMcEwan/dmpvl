`include "dff.vh"

// Pseudo-Random Number Generator as designed by David Blackman and Sebastian
// Vigna, but in synthesizable Verilog.
// This module only implements the state storage and next().
// No jump() or long_jump() functionallity, but the seed control interface
// allows these to be implemented externally if required.
module prngXoroshiro64s  (
  input  wire                       i_clk,
  input  wire                       i_rst,
  input  wire                       i_cg,

  input  wire                       i_seedValid,
  input  wire [31:0]                i_seedS0,
  input  wire [31:0]                i_seedS1,
  output wire [31:0]                o_s0,
  output wire [31:0]                o_s1,

  output wire [31:0]                o_result
);

localparam a = 26;
localparam b = 9;
localparam c = 13;

/*
uint32_t next(void) {
  const uint32_t s0 = s[0];
  uint32_t s1 = s[1];
  const uint32_t result = s0 * 0x9E3779BB;

  s1 ^= s0;
  s[0] = rotl(s0, 26) ^ s1 ^ (s1 << 9); // a, b
  s[1] = rotl(s1, 13); // c

  return result;
}
*/
wire [31:0] s0;
wire [31:0] s1;
`dff_cg_norst(reg [31:0], s0, i_clk, i_cg)
`dff_cg_norst(reg [31:0], s1, i_clk, i_cg)
`dff_cg_norst(reg [31:0], result, i_clk, i_cg)

always @* result_d = s0_q * 32'h9E3779BB; // const uint32_t result = s0 * 0x9E3779BB; TODO

assign s0 = s0_q;                     // const uint32_t s0 = s[0];
assign s1 = s0_q ^ s1_q;              // uint32_t s1 = s[1]; s1 ^= s0;

always @*
  if (i_seedValid)
    s0_d = i_seedS0;
  else
    // s[0] = rotl(s0, 26) ^ s1 ^ (s1 << 9); // a, b
    s0_d =
      {s0[31-a:0], s0[31:32-a]} ^
      s1 ^
      (s1 << b);
assign o_s0 = s0_q;

always @*
  if (i_seedValid)
    s1_d = i_seedS1;
  else
    // s[1] = rotl(s1, 13); // c
    s1_d = {s1[31-c:0], s1[31:32-c]};
assign o_s1 = s1_q;

assign o_result = result_q;

endmodule
