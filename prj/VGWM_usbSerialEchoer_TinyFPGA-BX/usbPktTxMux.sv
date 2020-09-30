
module usbPktTxMux (
  input           i_in_txPktBegin,
  input [3:0]     i_in_txPid,

  input           i_out_txPktBegin,
  input [3:0]     i_out_txPid,

  output          o_txPktBegin,
  output [3:0]    o_txPid
);

assign o_txPktBegin = i_in_txPktBegin | i_out_txPktBegin;
assign o_txPid = i_out_txPktBegin ? i_out_txPid : i_in_txPid;

endmodule
