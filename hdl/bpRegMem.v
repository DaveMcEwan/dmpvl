`include "dff.vh"

/* BytePipe interface, indended to sit on top of USB for register access.

- BytePipe has been designed with these goals:
  1. Very low cost to implement (approximately 17 dff, plus memory),
  2. Simple to reset to a known state.
  3. Simple and efficient mechanism for confirming that state *was* what you
     expected it to be as you update (functional monitoring).
  4. Efficient polling loops for non-linear sequences of addresses.

- All addressable locations are 1B wide.
- Address is up to 7b wide (up to 128 positions).
- Non-implemented addresses always read as 0.
  This allows all writeable bits to be discovered by writing `0xff` to each
  position, inspecting the result.
- All non-burst transactions generate 1B response.
- Write transaction sends cmd+address byte, then data byte, then receives 1B
  with previous/overwritten value at that address.
  The received value serves as a write-response to confirm that the write has
  taken place.
- Read transaction sends cmd+address byte, then receives 1B with the value at
  the previous address.
*/
module bpRegMem #(
  parameter ZERO_UNIMPL = 1, // Unimplemented locations return 0->unknown, 1->zero.
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

localparam ADDR_W = $clog2(N_REG);

`dff_cg_srst(reg, wr, i_clk, i_cg, i_rst, '0) // 1b FSM
`dff_cg_srst(reg, rd, i_clk, i_cg, i_rst, '0) // 1b FSM
`dff_cg_srst(reg [ADDR_W-1:0], addr, i_clk, i_cg, i_rst, '0)
`dff_cg_srst(reg [7:0], rdData, i_clk, i_cg, i_rst, '0)

// IO aliases
wire in_accepted = i_bp_valid && o_bp_ready;
wire out_accepted = o_bp_valid && i_bp_ready;
wire cmdWr = i_bp_data[7];
wire cmdRd = !i_bp_data[7];
wire [6:0] cmdAddr = i_bp_data[6:0];

wire txnBegin = !wr_q && in_accepted;
wire wrSet = txnBegin && cmdWr;
wire wrClr = wr_q && in_accepted;
wire rdSet = (txnBegin && cmdRd) || wrClr;
wire rdClr = out_accepted;

always @*
  if      (wrSet) wr_d = 1'b1;
  else if (wrClr) wr_d = 1'b0;
  else            wr_d = wr_q;

always @*
  if      (rdSet) rd_d = 1'b1;
  else if (rdClr) rd_d = 1'b0;
  else            rd_d = rd_q;

always @* addr_d = txnBegin ?
  cmdAddr[ADDR_W-1:0] :
  addr_q;

// Track validity of address to return zeros for out-of-range.
wire addrInRange;
generate if ((N_REG == 'd128) || (ZERO_UNIMPL == 0)) begin
  assign addrInRange = 1'b1;
end else begin
  localparam ADDR_HI = N_REG-1;

  `dff_cg_srst(reg, addrInRange, i_clk, i_cg, i_rst, '0)
  always @* addrInRange_d = txnBegin ?
    (ADDR_HI[6:0] >= cmdAddr) :
    addrInRange_q;

  assign addrInRange = addrInRange_q;
end endgenerate

(* mem2reg *) reg [7:0] memory_q [N_REG]; // dff_cg_norst
genvar i;
generate for (i = 0; i < N_REG; i=i+1) begin : reg_b
  localparam j = i;
  always @(posedge i_clk)
    if (i_cg && wrClr && (addr_q == j[ADDR_W-1:0]) && addrInRange)
      memory_q[i] <= i_bp_data;
end : reg_b endgenerate

always @*
  if (rdSet)
    rdData_d = addrInRange ? memory_q[addr_q] : '0;
  else
    rdData_d = rdData_q;

// Backpressure goes straight through so destination controls all flow, so the
// host must keep accepting data.
assign o_bp_ready = i_bp_ready;

assign o_bp_data = rdData_q;
assign o_bp_valid = rd_q;

endmodule
