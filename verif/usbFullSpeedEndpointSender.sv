`include "dff.svh"
`include "asrt.svh"

module usbFullSpeedEndpointSender #(
  parameter MAX_PKT = 8
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  output wire                       o_ready,
  input  wire                       i_valid,
  input  wire [7:0]                 i_data,

  output wire                       o_etStall,

  input  wire                       i_etReady,
  output wire                       o_etValid,
  output wire [8*MAX_PKT-1:0]       o_etData,
  output wire [$clog2(MAX_PKT):0]   o_etData_nBytes
);

wire accepted = o_ready && i_valid;
wire et_accepted = i_etReady && o_etValid;

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

// There are no halting conditions.
assign o_etStall = 1'b0;

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

endmodule
