`include "dff.vh"

/* BytePipe interface, indended to sit on top of USB for register access.
- Approximately 17 dff, plus memory.
- Address up to 128 positions.
- Each position is 1B wide.
- Start transaction with `{writeNotRead:1b, address:7b}`.
- Each transaction consists of sending a 2B request, and receiving 1B reply.
- Write transaction:
  1. Receive byte, `{writeNotRead:1b=1, address:7b}`
     Store the address.
     Valid is high so wait for next byte containing data.
  2. Receive byte `{data:8b}` is written to address, then the contents at
     address are read and returned.
- Read transaction:
  1. Receive byte, `{writeNotRead:1b=0, address:7b}`
     Store the address.
     Valid is low so then contents at (previous) address are read and returned.
  2. Receive byte, `{writeNotRead:1b=0, address:7b}`
     Store the address.
     Valid is low so then contents at (previous) address are read and returned.
- Read value for invalid/unimplemented bits should always be zero.
- All transactions return read data.
  This means all writeable bits can be discovered by writing `0xff` to each
  position, inspecting the result.
- Multiple reads can be combined.
*/
module bpRegMem #(
  parameter N_REG = 64  // in {1..128}. Number of registers to implement.
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

wire in_accepted = i_bp_valid && o_bp_ready;
wire out_accepted = o_bp_valid && i_bp_ready;

`dff_cg_srst(reg, wr, i_clk, i_cg, i_rst, '0)
`dff_cg_srst(reg, rd, i_clk, i_cg, i_rst, '0)

wire txnBegin = !wr_q && in_accepted;
wire wrBegin = txnBegin && i_bp_data[7];
wire wrEnd = wr_q && in_accepted;
wire rdBegin = (txnBegin && !wrBegin) || wrEnd;
wire rdEnd = out_accepted;

always @*
  if      (wrBegin) wr_d = 1'b1;
  else if (wrEnd)   wr_d = 1'b0;
  else              wr_d = wr_q;

always @*
  if      (rdBegin) rd_d = 1'b1;
  else if (rdEnd)   rd_d = 1'b0;
  else              rd_d = rd_q;

localparam ADDR_W = $clog2(N_REG);
`dff_cg_srst(reg [ADDR_W-1:0], addr, i_clk, i_cg && txnBegin, i_rst, '0)
always @* addr_d = i_bp_data[ADDR_W-1:0];

(* mem2reg *) reg [7:0] memory_m [N_REG];
always @ (posedge i_clk)
  if (wrEnd)
    memory_m[addr_q] <= i_bp_data;

`dff_cg_srst(reg [7:0], rdData, i_clk, i_cg && rdBegin, i_rst, '0)
always @* rdData_d = memory_m[addr_q];

// Backpressure goes straight through so destination controls all flow, so the
// host must keep accepting data.
assign o_bp_ready = i_bp_ready;

assign o_bp_data = rdData_q;
assign o_bp_valid = rd_q;

endmodule
