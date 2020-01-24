`include "dff.vh"

module fifo #(
  parameter WIDTH = 8,  // Must be 1 or more.
  parameter DEPTH = 8,  // Must be 2 or more.
  parameter FLOPSNOTMEM = 0
) (
  input  wire                       i_clk,
  input  wire                       i_rst,
  input  wire                       i_cg,

  input  wire                       i_flush,
  input  wire                       i_push,
  input  wire                       i_pop,

  input  wire [WIDTH-1:0]           i_data,
  output wire [WIDTH-1:0]           o_data,

  output wire                       o_empty,
  output wire                       o_full,

  output wire                       o_pushed,
  output wire                       o_popped,

  output wire [$clog2(DEPTH)-1:0]   o_wrptr,
  output wire [$clog2(DEPTH)-1:0]   o_rdptr,

  output wire [DEPTH-1:0]           o_valid,
  output wire [(DEPTH*WIDTH)-1:0]   o_entries // Only used with FLOPSNOTMEM.
);

localparam DEPTH_CLOG2 = $clog2(DEPTH);

genvar i;

// Onehot vectors for write and read enables.
wire [DEPTH-1:0] wr_vec;
wire [DEPTH-1:0] rd_vec;

// Control path.
`dff_cg_srst(reg [DEPTH_CLOG2-1:0], wrptr, i_clk, i_cg, i_rst, '0)
`dff_cg_srst(reg [DEPTH_CLOG2-1:0], rdptr, i_clk, i_cg, i_rst, '0)
`dff_cg_srst(reg [DEPTH-1:0],       valid, i_clk, i_cg, i_rst, '0)

// Data path, validated by valid_q.
generate if (FLOPSNOTMEM != 0) begin : flopsnotmemTrue

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

end : flopsnotmemTrue else begin : flopsnotmemFalse

  // Memory block typically will not have wire visibility for each bit.
  assign o_entries = '0; // unused

  reg [WIDTH-1:0] entries_m [DEPTH];

  always @ (posedge i_clk)
    if (i_cg && o_pushed)
      entries_m[wrptr_q] <= i_data;

  assign o_data = entries_m[rdptr_q];

end : flopsnotmemFalse endgenerate


wire doPush = !o_full && i_push;
wire doPop = !o_empty && i_pop;

assign o_pushed = doPush && !i_flush;
assign o_popped = doPop && !i_flush;

always @*
  if (i_flush)
    wrptr_d = '0;
  else if (doPush)
                                                  /* verilator lint_off WIDTH */
    wrptr_d = (wrptr_q == (DEPTH-1)) ? '0 : (wrptr_q + 1);
                                                  /* verilator lint_on  WIDTH */
  else
    wrptr_d = wrptr_q;
assign o_wrptr = wrptr_q;

always @*
  if (i_flush)
    rdptr_d = '0;
  else if (doPop)
                                                  /* verilator lint_off WIDTH */
    rdptr_d = (rdptr_q == (DEPTH-1)) ? '0 : (rdptr_q + 1);
                                                  /* verilator lint_on  WIDTH */
  else
    rdptr_d = rdptr_q;
assign o_rdptr = rdptr_q;


// Onehot rd/wr vectors.
generate for (i = 0; i < DEPTH; i=i+1) begin : vec_b
  assign wr_vec[i] = (wrptr_q == (i)) && doPush; // Set bit in valid_d/q
  assign rd_vec[i] = (rdptr_q == (i)) && doPop; // Clear bit in valid_d/q
end : vec_b endgenerate

always @* valid_d = ((valid_q & ~rd_vec) | wr_vec) & ~{DEPTH{i_flush}};
assign o_valid = valid_q;

assign o_empty = !(|valid_q);
assign o_full = &valid_q;

endmodule
