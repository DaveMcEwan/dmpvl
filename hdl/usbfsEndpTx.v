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


  input  wire                       i_etReady,
  output wire                       o_etValid,
  output wire                       o_etStall,

  // Write buffer interface to u_tx
  input  wire                         i_etTxAccepted,
  output wire                         o_etWrEn,
  output wire [$clog2(MAX_PKT)-1:0]   o_etWrIdx,
  output wire [7:0]                   o_etWrByte,
  output wire [$clog2(MAX_PKT+1)-1:0] o_etWrNBytes
);

localparam NBYTES_W = $clog2(MAX_PKT + 1);
localparam IDX_W = $clog2(MAX_PKT);

wire accepted = o_ready && i_valid;
wire et_accepted = i_etReady && o_etValid; // ACK received

`asrt(etTxAccepted, i_clk, !i_rst && i_etTxAccepted, i_valid)

`dff_nocg_srst(reg, writing, i_clk, i_rst, 1'b0)
always @*
  if (i_etTxAccepted)
    writing_d = 1'b1;
  else if (!i_valid || (o_etWrIdx == '1)) // No more data, OR sent MAX_PKT.
    writing_d = 1'b0; // NOTE: Relies on MAX_PKT being a power of 2.
  else
    writing_d = writing_q;

`dff_upcounter(reg [NBYTES_W-1:0], wrNBytes, i_clk, o_etWrEn, i_rst || et_accepted)

assign o_etValid = i_valid;

assign o_ready = writing_q;

assign o_etWrEn = writing_q && i_valid;
assign o_etWrIdx = wrNBytes_q[IDX_W-1:0];
assign o_etWrByte = i_data;
assign o_etWrNBytes = wrNBytes_q;

// There are no halting conditions.
assign o_etStall = 1'b0;

endmodule
