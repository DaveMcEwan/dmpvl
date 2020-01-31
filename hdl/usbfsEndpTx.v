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

  // TODO: rm
  output wire [8*MAX_PKT-1:0]       o_etData,
  output wire [$clog2(MAX_PKT):0]   o_etData_nBytes,

  // TODO: WIP
  // Write buffer interface to u_tx
  output wire                         o_etWrEn,
  output wire [$clog2(MAX_PKT)-1:0]   o_etWrIdx,
  output wire [7:0]                   o_etWrByte,
  output wire [$clog2(MAX_PKT+1)-1:0] o_etWrNBytes
);

localparam NBYTES_W = $clog2(MAX_PKT + 1);
localparam IDX_W = $clog2(MAX_PKT);

wire accepted = o_ready && i_valid;
wire et_accepted = i_etReady && o_etValid;






`dff_nocg_srst(reg, writing, i_clk, i_rst, 1'b0)
always @*
  if (et_accepted)
    writing_d = 1'b1;
  else if (!i_valid || (o_etWrIdx == '1)) // No more data, OR sent MAX_PKT.
    writing_d = 1'b0; // NOTE: Relies on MAX_PKT being a power of 2.
  else
    writing_d = writing_q;

`dff_upcounter(reg [NBYTES_W-1:0], wrNBytes, i_clk, o_etWrEn, i_rst || et_accepted)

//assign o_etValid = i_valid;

//assign o_ready = writing_q;

assign o_etWrEn = writing_q && i_valid;
assign o_etWrIdx = wrNBytes_q[IDX_W-1:0];
assign o_etWrByte = i_data;
assign o_etWrNBytes = wrNBytes_q;







`dff_nocg_srst(reg [$clog2(MAX_PKT):0], nBytes, i_clk, i_rst, '0)
always @*
  if (accepted)
    nBytes_d = nBytes_q + 'd1;
  else if (et_accepted)
    nBytes_d = 'd0;
  else
    nBytes_d = nBytes_q;

assign o_etData_nBytes = nBytes_q;

assign o_etValid = (nBytes_q != 'd0);

// Don't accept new data while current data is being taken.
assign o_ready = (nBytes_q < MAX_PKT) && !et_accepted;

genvar b;
`dff_nocg_srst(reg [8*MAX_PKT-1:0], data, i_clk, i_rst, '0)
generate for (b=0; b < MAX_PKT; b=b+1) begin
always @*
  if (accepted && (nBytes_q == b))
    data_d[8*b +: 8] = i_data;
  else
    data_d[8*b +: 8] = data_q[8*b +: 8];
end endgenerate

assign o_etData = data_q;





// There are no halting conditions.
assign o_etStall = 1'b0;

endmodule
