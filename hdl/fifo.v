`include "dff.vh"
`include "misc.vh"

module fifo #(
  parameter WIDTH = 8,  // Must be 1 or more.
  parameter DEPTH = 8,  // Must be 2 or more.
  parameter FLOPS_NOT_MEM = 0
) (
  input  wire                         i_clk,
  input  wire                         i_rst,
  input  wire                         i_cg,

  input  wire                         i_flush,
  input  wire                         i_push,
  input  wire                         i_pop,

  input  wire [WIDTH-1:0]             i_data,
  output wire [WIDTH-1:0]             o_data,

  output wire                         o_empty,
  output wire                         o_full,

  output wire                         o_pushed,
  output wire                         o_popped,

  output wire [$clog2(DEPTH)-1:0]     o_wrptr,
  output wire [$clog2(DEPTH)-1:0]     o_rdptr,

  output wire [DEPTH-1:0]             o_valid, // Only used with DEPTH < 4.
  output wire [$clog2(DEPTH + 1)-1:0] o_nEntries, // Only used with DEPTH >= 4.

  output wire [(DEPTH*WIDTH)-1:0]     o_entries // Only used with FLOPS_NOT_MEM.
);

localparam PTR_W = $clog2(DEPTH);
localparam CNT_W = $clog2(DEPTH + 1);

genvar i;

wire doPush = !o_full && i_push;
wire doPop = !o_empty && i_pop;
wire doFlush = i_cg && i_flush;

`dff_cg_srst(reg [PTR_W-1:0], wrptr, i_clk, i_cg && doPush, i_rst || doFlush, '0)
`dff_cg_srst(reg [PTR_W-1:0], rdptr, i_clk, i_cg && doPop,  i_rst || doFlush, '0)

// Onehot vectors for write and read enables.
wire [DEPTH-1:0] wr_vec;
wire [DEPTH-1:0] rd_vec;

generate if (FLOPS_NOT_MEM != 0) begin : useFlops

  (* mem2reg *) reg [WIDTH-1:0] entries_q [DEPTH]; // dff_cg_norst
  (* mem2reg *) reg [WIDTH-1:0] entries_d [DEPTH];

  for (i = 0; i < DEPTH; i=i+1) begin : entries_b

    always @*
      if (o_pushed && wr_vec[i])
        entries_d[i] = i_data;
      else
        entries_d[i] = entries_q[i];

    always @ (posedge i_clk)
      if (i_cg)
        entries_q[i] <= entries_d[i];

    assign o_entries[i*WIDTH +: WIDTH] = entries_q[i];

  end : entries_b

  assign o_data = entries_q[rdptr_q];

end : useFlops else begin : useMem

  // Memory block typically will not have wire visibility for each bit.
  assign o_entries = '0; // unused

  reg [WIDTH-1:0] entries_m [DEPTH];

  always @ (posedge i_clk)
    if (i_cg && o_pushed)
      entries_m[wrptr_q] <= i_data;

  assign o_data = entries_m[rdptr_q];

end : useMem endgenerate


assign o_pushed = doPush && !i_flush;
assign o_popped = doPop && !i_flush;

localparam MAXPTR = DEPTH - 1;
always @* wrptr_d = (wrptr_q == MAXPTR`LSb(PTR_W)) ? '0 : (wrptr_q + 'd1);
always @* rdptr_d = (rdptr_q == MAXPTR`LSb(PTR_W)) ? '0 : (rdptr_q + 'd1);
assign o_wrptr = wrptr_q;
assign o_rdptr = rdptr_q;


// Onehot rd/wr vectors.
generate for (i = 0; i < DEPTH; i=i+1) begin : vec_b
  assign wr_vec[i] = (wrptr_q == (i)) && doPush; // Set bit in valid_d/q
  assign rd_vec[i] = (rdptr_q == (i)) && doPop; // Clear bit in valid_d/q
end : vec_b endgenerate

generate if (DEPTH < 4) begin
  `dff_cg_srst(reg [DEPTH-1:0], valid, i_clk, i_cg, i_rst || doFlush, '0)
  always @* valid_d = (valid_q & ~rd_vec) | wr_vec;
  assign o_valid = valid_q;
  assign o_nEntries = '0;

  assign o_empty = !(|valid_q);
  assign o_full = &valid_q;
end else begin
  // NOTE: o_valid/valid_q should only be used where DEPTH < 4.
  // Disable valid_q and use a counter instead for empty/full.
  // Deep fifos would require too many LUTs because OR/AND tree depth for
  // empty/full calculation would be log(DEPTH) instead of log(log(DEPTH)).
  assign o_valid = '0;

  `dff_cg_srst(reg [CNT_W-1:0], nEntries, i_clk, i_cg, i_rst || doFlush, '0)
  always @*
    if (doPush && !doPop)
      nEntries_d = nEntries_q + 'd1;
    else if (!doPush && doPop)
      nEntries_d = nEntries_q - 'd1;
    else
      nEntries_d = nEntries_q;

  assign o_nEntries = nEntries_q;

  assign o_empty = (nEntries_q == '0);
  assign o_full = (nEntries_q == DEPTH);
end endgenerate

endmodule
