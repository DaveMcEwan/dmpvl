
// USB Full Speed protocol engine
// Instanciates all the endpoints, making arrays of in,out end point signals.

module usbPe #(
  parameter N_EP_OUT = 1,
  parameter N_EP_IN = 1,
  parameter MAX_OUT_PACKET_SIZE = 8, // Must be in {8,16,32}.
  parameter MAX_IN_PACKET_SIZE = 32  // Must be in {16,32}
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  input  wire [6:0]                 i_devAddr,

  input  wire [N_EP_OUT-1:0]        i_outEp_req,
  output wire [N_EP_OUT-1:0]        o_outEp_grant,
  output wire [N_EP_OUT-1:0]        o_outEp_dataAvail,
  output wire [N_EP_OUT-1:0]        o_outEp_setup,
  input  wire [N_EP_OUT-1:0]        i_outEp_dataGet,
  output wire [7:0]                 o_outEp_data,
  output wire [N_EP_OUT-1:0]        o_outEp_acked,

  input  wire [N_EP_IN-1:0]         i_inEp_req,
  output wire [N_EP_IN-1:0]         o_inEp_grant,
  output wire [N_EP_IN-1:0]         o_inEp_dataFree,
  input  wire [N_EP_IN-1:0]         i_inEp_dataPut,
  input  wire [(N_EP_IN*8)-1:0]     i_inEp_data,
  input  wire [N_EP_IN-1:0]         i_inEp_dataDone,
  input  wire [N_EP_IN-1:0]         i_inEp_stall,
  output wire [N_EP_IN-1:0]         o_inEp_acked,

  output wire                       o_usbTx_p,
  output wire                       o_usbTx_n,
  output wire                       o_usbTxEn,
  input  wire                       i_usbRx_p,
  input  wire                       i_usbRx_n
);

wire [7:0] inEp_arbData;
wire bitStrobe;   // Synchronise rx and tx.
wire rxPktBegin;
wire rxPktEnd;
wire [3:0] rxPid;
wire [6:0] rxAddr;
wire [3:0] rxEndp;
wire [10:0] rxFrameNum;
wire rxDataPut;
wire [7:0] rxData;
wire rxPktValid;
wire inTxPktBegin;
wire [3:0] inTxPid;
wire outTxPktBegin;
wire [3:0] outTxPid;
wire txPktBegin;
wire txPktEnd;
wire [3:0] txPid;
wire txDataAvail;
wire txDataGet;
wire [7:0] txData;
/* verilator lint_off UNOPTFLAT */
wire [N_EP_OUT-1:0] outEp_grant;
/* verilator lint_on  UNOPTFLAT */

assign o_outEp_grant = outEp_grant;

usbEpInArbiter #(
  .N_EP_IN(N_EP_IN)
) u_usbEpInArbiter (
  .i_inEp_req     (i_inEp_req),
  .o_inEp_grant   (o_inEp_grant),
  .i_inEp_data    (i_inEp_data),
  .o_inEp_arbData (inEp_arbData)
);

usbEpOutArbiter #(
  .N_EP_OUT   (N_EP_OUT)
) u_usbEpOutArbiter (
  .i_outEp_req    (i_outEp_req),
  .o_outEp_grant  (outEp_grant)
);

usbPeIn #(
  .N_EP_IN            (N_EP_IN),
  .MAX_IN_PACKET_SIZE (MAX_IN_PACKET_SIZE)
) u_usbPeIn (
  .i_clk              (i_clk),
  .i_rst              (i_rst),

  .i_devAddr          (i_devAddr),

  .o_inEp_dataFree    (o_inEp_dataFree),
  .i_inEp_dataPut     (i_inEp_dataPut),
  .i_inEp_data        (inEp_arbData),
  .i_inEp_dataDone    (i_inEp_dataDone),
  .i_inEp_stall       (i_inEp_stall),
  .o_inEp_acked       (o_inEp_acked),

  .i_rxPktBegin       (rxPktBegin),
  .i_rxPktEnd         (rxPktEnd),
  .i_rxPktValid       (rxPktValid),
  .i_rxPid            (rxPid),
  .i_rxAddr           (rxAddr),
  .i_rxEndp           (rxEndp),
  .i_rxFrameNum       (rxFrameNum),

  .o_txPktBegin       (inTxPktBegin),
  .i_txPktEnd         (txPktEnd),
  .o_txPid            (inTxPid),
  .o_txDataAvail      (txDataAvail),
  .i_txDataGet        (txDataGet),
  .o_txData           (txData)
);

usbPeOut #(
  .N_EP_OUT             (N_EP_OUT),
  .MAX_OUT_PACKET_SIZE  (MAX_OUT_PACKET_SIZE)
) u_usbPeOut (
  .i_clk              (i_clk),
  .i_rst              (i_rst),

  .i_devAddr          (i_devAddr),

  .o_outEp_dataAvail  (o_outEp_dataAvail),
  .o_outEp_setup      (o_outEp_setup),
  .i_outEp_dataGet    (i_outEp_dataGet),
  .o_outEp_data       (o_outEp_data),
  .o_outEp_acked      (o_outEp_acked),
  .i_outEp_grant      (outEp_grant),

  .i_rxPktBegin       (rxPktBegin),
  .i_rxPktEnd         (rxPktEnd),
  .i_rxPktValid       (rxPktValid),
  .i_rxPid            (rxPid),
  .i_rxAddr           (rxAddr),
  .i_rxEndp           (rxEndp),
  .i_rxFrameNum       (rxFrameNum),
  .i_rxDataPut        (rxDataPut),
  .i_rxData           (rxData),

  .o_txPktBegin       (outTxPktBegin),
  .i_txPktEnd         (txPktEnd),
  .o_txPid            (outTxPid)
);

usbPktRx u_usbPktRx (
  .i_clk_48MHz        (i_clk),
  .i_rst              (i_rst),
  .i_dp               (i_usbRx_p),
  .i_dn               (i_usbRx_n),
  .o_bitStrobe        (bitStrobe),
  .o_pktBegin         (rxPktBegin),
  .o_pktEnd           (rxPktEnd),
  .o_pid              (rxPid),
  .o_addr             (rxAddr),
  .o_endp             (rxEndp),
  .o_frameNum         (rxFrameNum),
  .o_dataPut          (rxDataPut),
  .o_data             (rxData),
  .o_pktValid         (rxPktValid)
);

usbPktTxMux u_usbPktTxMux (
  .i_in_txPktBegin    (inTxPktBegin),
  .i_in_txPid         (inTxPid),

  .i_out_txPktBegin   (outTxPktBegin),
  .i_out_txPid        (outTxPid),

  .o_txPktBegin       (txPktBegin),
  .o_txPid            (txPid)
);

usbPktTx u_usbPktTx (
  .i_clk_48MHz        (i_clk),
  .i_rst              (i_rst),
  .i_bitStrobe        (bitStrobe),
  .o_oe               (o_usbTxEn),
  .o_dp               (o_usbTx_p),
  .o_dn               (o_usbTx_n),
  .i_pktBegin         (txPktBegin),
  .o_pktEnd           (txPktEnd),
  .i_pid              (txPid),
  .i_txDataAvail      (txDataAvail),
  .o_txDataGet        (txDataGet),
  .i_txData           (txData)
);

endmodule
