`include "dff.svh"
`include "misc.svh"

module fifo #(
  parameter WIDTH = 8,  // Must be 1 or more.
  parameter DEPTH = 8,  // Must be 2 or more.
  parameter FLOPS_NOT_MEM = 0, // 0 -> RAM, 1 -> FFs

  // 0 -> Allow nEntries_q to be removed in synthesis iff o_nEntries is unconnected.
  //      Handshake outputs (o_ready/!full, o_valid/!empty) from pointer comparison.
  // 1 -> nEntries_q cannot be removed as this is used for handshake outputs.
  parameter FORCEKEEP_NENTRIES = 0
) (
  input  wire                         i_clk,
  input  wire                         i_rst,
  input  wire                         i_cg,

  input  wire                         i_flush,

  input  wire [WIDTH-1:0]             i_data,
  input  wire                         i_valid, // push
  output wire                         o_ready, // !full

  output wire [WIDTH-1:0]             o_data,
  output wire                         o_valid, // !empty
  input  wire                         i_ready, // pop

  output wire                         o_pushed,
  output wire                         o_popped,

  output wire [$clog2(DEPTH)-1:0]     o_wptr,
  output wire [$clog2(DEPTH)-1:0]     o_rptr,

  output wire [DEPTH-1:0]             o_validEntries, // Only used with DEPTH < 4.
  output wire [$clog2(DEPTH + 1)-1:0] o_nEntries, // Only used with DEPTH >= 4.

  output wire [(DEPTH*WIDTH)-1:0]     o_entries // Only used with FLOPS_NOT_MEM.
);

localparam PTR_W = $clog2(DEPTH);
localparam CNT_W = $clog2(DEPTH + 1);
localparam MAXPTR = DEPTH - 1;
localparam DEPTH_ISPOW2 = ((DEPTH & (DEPTH-1)) == 0);

genvar i;

wire doPush = o_ready && i_valid;
wire doPop = o_valid && i_ready;
wire doFlush = i_cg && i_flush;

assign o_pushed = doPush && !i_flush;
assign o_popped = doPop && !i_flush;

`dff_cg_srst(reg [PTR_W:0], wptr, i_clk, i_cg && doPush, i_rst || doFlush, '0)
`dff_cg_srst(reg [PTR_W:0], rptr, i_clk, i_cg && doPop,  i_rst || doFlush, '0)
assign o_wptr = wptr_q`LSb(PTR_W);
assign o_rptr = rptr_q`LSb(PTR_W);

generate if (DEPTH_ISPOW2) begin
  // Funtionally equivalent to non-pow2 case but easier for synth tools.
  always @* wptr_d = wptr_q + 'd1;
  always @* rptr_d = rptr_q + 'd1;
end else begin
  wire wptrWrap = (o_wptr == MAXPTR`LSb(PTR_W));
  wire rptrWrap = (o_rptr == MAXPTR`LSb(PTR_W));
  always @* wptr_d`LSb(PTR_W) = wptrWrap ? '0 : (o_wptr + 'd1);
  always @* rptr_d`LSb(PTR_W) = rptrWrap ? '0 : (o_rptr + 'd1);
  always @* wptr_d[PTR_W] = wptrWrap ? !wptr_q[PTR_W] : wptr_q[PTR_W];
  always @* rptr_d[PTR_W] = rptrWrap ? !rptr_q[PTR_W] : rptr_q[PTR_W];
end endgenerate

// Onehot vectors for write and read enables.
wire [DEPTH-1:0] wr_vec;
wire [DEPTH-1:0] rd_vec;
generate for (i = 0; i < DEPTH; i=i+1) begin : vec_b
  assign wr_vec[i] = (o_wptr == (i)) && doPush; // Set bit in valid_d/q
  assign rd_vec[i] = (o_rptr == (i)) && doPop; // Clear bit in valid_d/q
end : vec_b endgenerate

generate if (DEPTH < 4) begin
  `dff_cg_srst(reg [DEPTH-1:0], valid, i_clk, i_cg, i_rst || doFlush, '0)
  always @* valid_d = (valid_q & ~rd_vec) | wr_vec;
  assign o_validEntries = valid_q;
  assign o_nEntries = '0;

  assign o_valid = |valid_q;
  assign o_ready = !(&valid_q);
end else begin
  // NOTE: o_validEntries/valid_q should only be used where DEPTH < 4.
  // Disable valid_q and use a counter instead for empty/full.
  // Deep fifos would require too many LUTs because OR/AND tree depth for
  // empty/full calculation would be log(DEPTH) instead of log(log(DEPTH)).
  assign o_validEntries = '0;

  `dff_cg_srst(reg [CNT_W-1:0], nEntries, i_clk, i_cg, i_rst || doFlush, '0)
  always @*
    if (doPush && !doPop)
      nEntries_d = nEntries_q + 'd1;
    else if (!doPush && doPop)
      nEntries_d = nEntries_q - 'd1;
    else
      nEntries_d = nEntries_q;

  assign o_nEntries = nEntries_q;

  if (FORCEKEEP_NENTRIES) begin
    assign o_valid = (nEntries_q != '0);
    assign o_ready = (nEntries_q != DEPTH);
  end else begin
    wire ptrsUnequal = (o_wptr != o_rptr);
    wire ptrsWrapped = (wptr_q[PTR_W] != rptr_q[PTR_W]);

    assign o_valid = ptrsUnequal || ptrsWrapped; // !empty
    assign o_ready = ptrsUnequal || !ptrsWrapped; // !full
  end
end endgenerate

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

  assign o_data = entries_q[o_rptr];

end : useFlops else begin : useMem

  // Memory block typically will not have wire visibility for each bit.
  assign o_entries = '0; // unused

  reg [WIDTH-1:0] entries_m [DEPTH];

  always @ (posedge i_clk)
    if (i_cg && o_pushed)
      entries_m[o_wptr] <= i_data;

  assign o_data = entries_m[o_rptr];

end : useMem endgenerate

endmodule
