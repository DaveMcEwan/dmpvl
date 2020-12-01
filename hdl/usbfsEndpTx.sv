`include "dff.svh"
`include "asrt.svh"

module usbfsEndpTx #(
  parameter NAK_NOT_ZEROLENGTHDATA = 0, // NOTE: NAK is poorly tested.
  parameter MAX_PKT = 8
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  output wire                       o_ready,
  input  wire                       i_valid,
  input  wire [7:0]                 i_data,


  input  wire                       i_etReady,
  output wire                       o_etValid,
  output wire                       o_etStall,

  // Write buffer interface to u_tx
  input  wire                         i_etTxAccepted, // Pulse high when pid[DATA*] byte has been sent by u_tx.
  output wire                         o_etWrEn,
  output wire [$clog2(MAX_PKT)-1:0]   o_etWrIdx,
  output wire [7:0]                   o_etWrByte
);

localparam MAX_IDX = MAX_PKT - 1;
localparam IDX_W = $clog2(MAX_PKT);

wire accepted = o_ready && i_valid;
wire et_accepted = i_etReady && o_etValid; // ACK received

wire fifo_o_valid;
wire _unused_fifo_o_pushed;
wire _unused_fifo_o_wptr;
wire _unused_fifo_o_rptr;
wire [1:0] _unused_fifo_o_validEntries;
wire [1:0] _unused_fifo_o_nEntries;
wire [15:0] _unused_fifo_o_entries;

`dff_nocg_srst(reg, writing, i_clk, i_rst, 1'b0)

fifo #(
  .WIDTH          (8),
  .DEPTH          (2),
  .FLOPS_NOT_MEM  (1)
) u_fifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1),

  .i_flush    (1'b0),

  .i_data     (i_data),
  .i_valid    (i_valid),
  .o_ready    (o_ready),

  .o_data     (o_etWrByte),
  .o_valid    (fifo_o_valid),
  .i_ready    (writing_q),

  .o_pushed   (_unused_fifo_o_pushed),
  .o_popped   (o_etWrEn),

  .o_wptr     (_unused_fifo_o_wptr),
  .o_rptr     (_unused_fifo_o_rptr),

  .o_validEntries (_unused_fifo_o_validEntries),
  .o_nEntries     (_unused_fifo_o_nEntries),

  .o_entries  (_unused_fifo_o_entries)
);

// No more data, OR sent MAX_PKT.
wire writing_goDn = !fifo_o_valid || (o_etWrIdx == MAX_IDX[IDX_W-1:0]);
always @*
  if (i_etTxAccepted)
    writing_d = 1'b1;
  else if (writing_goDn)
    writing_d = 1'b0;
  else
    writing_d = writing_q;

wire wrIdx_incr = o_etWrEn;
wire wrIdx_zero = writing_goDn; // Clear at end of packet.
`dff_upcounter(reg [IDX_W-1:0], wrIdx, i_clk, wrIdx_incr, i_rst || wrIdx_zero)
assign o_etWrIdx = wrIdx_q;

generate if (NAK_NOT_ZEROLENGTHDATA) begin
  `dff_nocg_srst(reg, etValid, i_clk, i_rst, 1'b0)
  always @*
    if (fifo_o_valid)
      etValid_d = 1'b1;
    else if (et_accepted)
      etValid_d = 1'b0;
    else
      etValid_d = etValid_q;

  assign o_etValid = etValid_q;
end else begin
  // Host can read 0-length data packets instead of NAK.
  assign o_etValid = 1'b1;
end endgenerate

// There are no halting conditions.
assign o_etStall = 1'b0;

endmodule
