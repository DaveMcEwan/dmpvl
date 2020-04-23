`include "dff.vh"

/* BytePipe interface, indended to sit on top of USB for register access.

- BytePipe has been designed with these goals:
  1. Very low cost to implement (approximately 17 dff, plus memory),
  2. Simple to reset to a known state.
  3. Simple and efficient mechanism for confirming that state *was* what you
     expected it to be as you update (functional monitoring).
  4. Efficient polling loops for non-linear sequences of addresses.

- All transactions generate 1B response.
- All addressable locations are 1B wide.
- Address is up to 7b wide (up to 128 positions).
- Non-implemented addresses always read as 0.
  This allows all writeable bits to be discovered by writing `0xff` to each
  position, inspecting the result.
- Write transaction sends cmd+address byte, then data byte, then receives 1B
  with previous/overwritten value at that address.
- Read transaction sends cmd+address byte, then receives 1B with the value at
  the previous address.
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
`dff_cg_srst(reg [ADDR_W-1:0], addr, i_clk, i_cg && txnBegin, i_rst, '0)
always @* addr_d = i_bp_data[ADDR_W-1:0];

// Track validity of address to return zeros for out-of-range.
wire addrInRange;
generate if (ADDR_W == 'd7) begin
  assign addrInRange = 1'b1;
end else begin
  localparam N_REG_= N_REG;

  `dff_cg_srst(reg, addrInRange, i_clk, i_cg && txnBegin, i_rst, '0)
  always @* addrInRange_d = (i_bp_data[6:0] < N_REG_[6:0]);

  assign addrInRange = addrInRange_q;
end endgenerate

(* mem2reg *) reg [7:0] memory_q [N_REG]; // dff_cg_norst
genvar i;
generate for (i = 0; i < N_REG; i=i+1) begin : reg_b
  always @(posedge i_clk)
    if (i_cg && wrEnd && (addr_q == i) && addrInRange)
      memory_q[i] <= i_bp_data;
end : reg_b endgenerate

`dff_cg_srst(reg [7:0], rdData, i_clk, i_cg && rdBegin, i_rst, '0)
always @* rdData_d = addrInRange ? memory_q[addr_q] : '0;

// Backpressure goes straight through so destination controls all flow, so the
// host must keep accepting data.
assign o_bp_ready = i_bp_ready;

assign o_bp_data = rdData_q;
assign o_bp_valid = rd_q;

endmodule
