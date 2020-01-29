`include "dff.vh"
`include "asrt.vh"

module usbFullSpeedEndpointReceiver #(
  parameter MAX_PKT = 8
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  input  wire                       i_ready,
  output wire                       o_valid,
  output wire [7:0]                 o_data,

  output wire                       o_erStall,

  output wire                       o_erReady,
  input  wire                       i_erValid,
  input  wire [8*MAX_PKT-1:0]       i_erData,
  input  wire [$clog2(MAX_PKT):0]   i_erData_nBytes
);

wire accepted = i_ready && o_valid;
wire er_accepted = o_erReady && i_erValid;

`dff_cg_srst(reg [$clog2(MAX_PKT):0], nBytes_topush, i_clk, er_accepted, i_rst, '0)
always @* nBytes_topush_d = i_erData_nBytes;

// Number of bytes pushed into fifo.
`dff_nocg_srst(reg [$clog2(MAX_PKT):0], nBytes_pushed, i_clk, i_rst, '0)
always @*
  if (push)
    nBytes_pushed_d = nBytes_pushed_q + 'd1;
  else if (er_accepted)
    nBytes_pushed_d = 'd0;
  else
    nBytes_pushed_d = nBytes_pushed_q;

// {{{ fifo
wire push = (nBytes_pushed_q != nBytes_topush_q);
wire empty;
fifo #(
  .WIDTH          (8),
  .DEPTH          (2),
  .FLOPS_NOT_MEM  (0)
) u_fifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1),

  .i_flush    (1'b0), // unused
  .i_push     (push),
  .i_pop      (accepted),

  .i_data     (i_erData[8*nBytes_pushed_q +: 8]),
  .o_data     (o_data),

  .o_empty    (empty),
  .o_full     (),

  .o_pushed   (),
  .o_popped   (),

  .o_wrptr    (),
  .o_rdptr    (),

  .o_valid    (), // unused
  .o_nEntries (), // unused

  .o_entries  ()  // unused
);
// }}} fifo

// Must have space for a full packet.
assign o_erReady = empty;

assign o_valid = !empty;

// There are no halting conditions.
assign o_erStall = 1'b0;

endmodule
