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
  parameter N_REG = 64  // in {2..128}. Number of registers to implement.
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
`dff_nocg_srst(reg [ADDR_W-1:0], addr, i_clk, i_rst, '0)
always @*
  if (i_cg && txnBegin)
    addr_d = i_bp_data[ADDR_W-1:0];
  else
    addr_d = addr_q;

// Track validity of address to return zeros for out-of-range.
wire addrInRange;
generate if (ADDR_W == 'd7) begin
  assign addrInRange = 1'b1;
end else begin
  localparam N_REG_= N_REG;

  `dff_nocg_srst(reg, addrInRange, i_clk, i_rst, '0)
  always @*
    if (i_cg && txnBegin)
      addrInRange_d = (i_bp_data[6:0] < N_REG_[6:0]);
    else
      addrInRange_d = addrInRange_q;

  assign addrInRange = addrInRange_q;
end endgenerate

(* mem2reg *) reg [7:0] memory_d [N_REG];
(* mem2reg *) reg [7:0] memory_q [N_REG]; // dff_cg_norst
genvar i;
generate for (i = 0; i < N_REG; i=i+1) begin : reg_b
  always @*
    if (i_cg && wrEnd && (addr_q == i) && addrInRange)
      memory_d[i] = i_bp_data;
    else
      memory_d[i] = memory_q[i];

  always @(posedge i_clk)
      memory_q[i] <= memory_d[i];
end : reg_b endgenerate

`dff_cg_srst(reg [7:0], rdData, i_clk, i_cg && rdBegin, i_rst, '0)
always @* rdData_d = addrInRange ? memory_q[addr_q] : '0;

// Backpressure goes straight through so destination controls all flow, so the
// host must keep accepting data.
assign o_bp_ready = i_bp_ready;

assign o_bp_data = rdData_q;
assign o_bp_valid = rd_q;

endmodule
