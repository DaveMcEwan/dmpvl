`include "dff.vh"
`include "asrt.vh"

module usbfsEndpTx #(
  parameter MAX_PKT = 8
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  output wire                       o_ready,
  input  wire                       i_valid,
  input  wire [7:0]                 i_data,


  input  wire                       i_etReady, // Host has taken something.
  output wire                       o_etValid, // Endpoint has something to give.
  output wire                       o_etStall,

  // Write buffer interface to u_tx
  input  wire                         i_etTxAccepted, // Pulse high when pid[DATA*] byte has been sent by u_tx.
  output wire                         o_etWrEn,
  output wire [$clog2(MAX_PKT)-1:0]   o_etWrIdx,
  output wire [7:0]                   o_etWrByte
);

wire accepted = o_ready && i_valid;
wire et_accepted = i_etReady && o_etValid; // ACK received

wire fifo_o_empty;
wire fifo_o_full;
wire _unused_fifo_o_pushed;
wire _unused_fifo_o_wrptr;
wire _unused_fifo_o_rdptr;
wire [1:0] _unused_fifo_o_valid;
wire [1:0] _unused_fifo_o_nEntries;
wire [15:0] _unused_fifo_o_entries;

fifo #(
  .WIDTH          (8),
  .DEPTH          (2),
  .FLOPS_NOT_MEM  (1)
) u_fifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1),

  .i_flush    (1'b0),
  .i_push     (i_valid),
  .i_pop      (writing_q),

  .i_data     (i_data),
  .o_data     (o_etWrByte),

  .o_empty    (fifo_o_empty),
  .o_full     (fifo_o_full),

  .o_pushed   (_unused_fifo_o_pushed),
  .o_popped   (o_etWrEn),

  .o_wrptr    (_unused_fifo_o_wrptr),
  .o_rdptr    (_unused_fifo_o_rdptr),

  .o_valid    (_unused_fifo_o_valid),
  .o_nEntries (_unused_fifo_o_nEntries),

  .o_entries  (_unused_fifo_o_entries)
);
assign o_ready = !fifo_o_full;

// When this goes (and stays) high the transactor will eventually assert
// i_etTxAccepted for a cycle which starts the writing/wrIdx FSM.
assign o_etValid = !fifo_o_empty;

// No more data, OR sent MAX_PKT.
// NOTE: Relies on MAX_PKT being a power of 2 (required by USB spec).
wire writing_goDn = !fifo_o_empty || (o_etWrIdx == '1);

`dff_nocg_srst(reg, writing, i_clk, i_rst, 1'b0)
always @*
  if (i_etTxAccepted)
    writing_d = 1'b1;
  else if (writing_goDn)
    writing_d = 1'b0;
  else
    writing_d = writing_q;

wire wrIdx_incr = o_etWrEn;
wire wrIdx_zero = writing_goDn; // Clear at end of packet.
localparam IDX_W = $clog2(MAX_PKT);
`dff_upcounter(reg [IDX_W-1:0], wrIdx, i_clk, wrIdx_incr, i_rst || wrIdx_zero)
assign o_etWrIdx = wrIdx_q;

// There are no halting conditions.
assign o_etStall = 1'b0;

endmodule
