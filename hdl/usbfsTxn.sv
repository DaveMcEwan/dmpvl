`include "asrt.svh"
`include "dff.svh"
`include "usbSpec.svh"

module usbfsTxn #(
  // Number of endpoints >=1. Endpoint0 is always the Default Endpoint (control).
  parameter RX_N_ENDP = 2,
  parameter TX_N_ENDP = 2,

  // Isochronous endpoints don't handshake.
  parameter RX_ISOCHRONOUS = 0, // Bit per rx (OUT) endpoint.
  parameter TX_ISOCHRONOUS = 0, // Bit per tx (IN) endpoint.

  // 0=Ignore i_*xStall. 1=Implement logic for stalling endpoints.
  parameter RX_STALLABLE = 2'b00, // Bit per rx (OUT) endpoint.
  parameter TX_STALLABLE = 2'b01, // Bit per tx (IN) endpoint.

  parameter MAX_PKT = 8  // in {8,16,32,64}. wMaxPacketSize
) (
  input  wire                       i_clk_48MHz,
  input  wire                       i_rst,

  // USB {d+, d-}, output enable.
  input  wire                       i_dp,
  input  wire                       i_dn,
  output wire                       o_dp,
  output wire                       o_dn,
  output wire                       o_oe,

  // Endpoints receiving data
  input  wire [RX_N_ENDP-1:0]       i_erReady,
  output wire [RX_N_ENDP-1:0]       o_erValid,
  input  wire [RX_N_ENDP-1:0]       i_erStall, // Masked with RX_STALLABLE

  // Read buffer interface
  // Read enable and index signals in format {endpN_*, ..., endp0_*}
  input  wire [RX_N_ENDP-1:0]                 i_erRdEn,
  input  wire [RX_N_ENDP*$clog2(MAX_PKT)-1:0] i_erRdIdx,
  output wire [7:0]                           o_erRdByte,
  output wire [$clog2(MAX_PKT+1)-1:0]         o_erRdNBytes,

  // Endpoints transmitting data
  output wire [TX_N_ENDP-1:0]       o_etReady,
  input  wire [TX_N_ENDP-1:0]       i_etValid,
  input  wire [TX_N_ENDP-1:0]       i_etStall, // Masked with TX_STALLABLE

  // Write buffer interface
  // All signals in format {endpN_*, ..., endp0_*}
  output wire [TX_N_ENDP-1:0]                   o_etTxAccepted,
  input  wire [TX_N_ENDP-1:0]                   i_etWrEn,
  input  wire [TX_N_ENDP*$clog2(MAX_PKT)-1:0]   i_etWrIdx,
  input  wire [TX_N_ENDP*8-1:0]                 i_etWrByte,

  // Current state of transaction flags $onehot({SETUP, OUT, IN}).
  output wire [2:0]                 o_txnType,

  // Current frame number.
  // NOTE: Endpoints are not required to do anything with this.
  // Host-mode --> Counter value.
  // Device-mode --> Frame number from token[SOF].
  output wire [10:0]                o_frameNumber,

  // Dev-mode input comes from endpoint0.
  // Device address, initially the Default Address (0), but configured with a
  // Setup transfer to the Default Endpoint (0).
  input  wire [6:0]                 i_devAddr
);


localparam DATA_W = 8*MAX_PKT;
localparam NBYTES_W = $clog2(MAX_PKT + 1);
localparam RDIDX_W = $clog2(MAX_PKT);
localparam WRIDX_W = $clog2(MAX_PKT);

genvar e;

wire er_accepted = |(i_erReady & o_erValid);
wire et_accepted = |(o_etReady & i_etValid);

// {{{ u_rd, u_tx

wire strobe_12MHz;

wire                      rx_eop;
wire                      rx_inflight;
wire [3:0]                rx_pid;
wire [6:0]                rx_addr;
wire [3:0]                rx_endp;
wire [7:0]                rx_rdByte;
wire [NBYTES_W-1:0]       rx_rdNBytes;
wire                      rx_pidOkay;
wire                      rx_tokenOkay;
wire                      rx_dataOkay;

wire                      tx_inflight;
wire                      tx_ready;
wire                      tx_valid;
wire                      tx_eopDone;
wire [3:0]                tx_pid;

// u_tx.o_ready changes at slower rate than transactor clock so detect falling
// edge of accepted.
`dff_nocg_srst(reg, tx_acceptance, i_clk_48MHz, i_rst, 1'b0)
always @* tx_acceptance_d = tx_ready && tx_valid;
wire tx_accepted = !tx_acceptance_d && tx_acceptance_q;

usbfsPktRx #(
  .MAX_PKT          (MAX_PKT)
) u_rx (
  .i_clk_48MHz          (i_clk_48MHz),
  .i_rst                (i_rst),

  .i_dp                 (i_dp),
  .i_dn                 (i_dn),

  .o_strobe_12MHz       (strobe_12MHz),
  .o_eop                (rx_eop),
  .o_inflight           (rx_inflight),

  .o_pid                (rx_pid),
  .o_addr               (rx_addr),
  .o_endp               (rx_endp),

  .i_clk_rd             (i_clk_48MHz),
  .i_rdEn               (erRdEn),
  .i_rdIdx              (erRdIdx),
  .o_rdByte             (o_erRdByte),
  .o_rdNBytes           (o_erRdNBytes),

  .o_pidOkay            (rx_pidOkay),
  .o_tokenOkay          (rx_tokenOkay),
  .o_dataOkay           (rx_dataOkay)
);

usbfsPktTx #(
  .MAX_PKT          (MAX_PKT)
) u_tx (
  .i_clk_48MHz              (i_clk_48MHz),
  .i_strobe_12MHz           (strobe_12MHz),
  .i_rst                    (i_rst),

  .o_ready                  (tx_ready),
  .i_valid                  (tx_valid),

  .o_eopDone                (tx_eopDone),

  .i_pid                    (tx_pid),

  .i_wrEn                   (etWrEn),
  .i_wrIdx                  (etWrIdx),
  .i_wrByte                 (etWrByte),

  .o_dp                     (o_dp),
  .o_dn                     (o_dn),
  .o_inflight               (tx_inflight)
);

assign o_erRdByte = rx_rdByte;
assign o_erRdNBytes = rx_rdNBytes;

assign o_oe = tx_inflight || tosend_q;

// }}} u_rd, u_tx

// {{{ PID rx/tx decode

wire [1:0] rx_pidCodingGroup = rx_pid[1:0];
wire rx_pidGrp_isToken     = (rx_pidCodingGroup == PIDGROUP_TOKEN);
wire rx_pidGrp_isData      = (rx_pidCodingGroup == PIDGROUP_DATA);
wire rx_pidGrp_isHandshake = (rx_pidCodingGroup == PIDGROUP_HANDSHAKE);

wire [2:0] rx_pidGrp = {
  rx_pidGrp_isToken,
  rx_pidGrp_isData,
  rx_pidGrp_isHandshake
};
`asrt(rx_pidGrp, i_clk_48MHz, !i_rst, $onehot0(rx_pidGrp))

wire rcvdPidOkay = rx_eop && rx_pidOkay;
wire rcvd_isToken      = rcvdPidOkay && rx_pidGrp_isToken && rx_tokenOkay;
wire rcvd_isData       = rcvdPidOkay && rx_pidGrp_isData && rx_dataOkay;
wire rcvd_isHandshake  = rcvdPidOkay && rx_pidGrp_isHandshake;

// NOTE: Only the non-pidgroup bits are required since rcvd_* has already
// taken pidgroup bits into consideration.
wire rcvdToken_in     = rcvd_isToken && (rx_pid[3:2] == PID_TOKEN_IN[3:2]);
wire rcvdToken_out    = rcvd_isToken && (rx_pid[3:2] == PID_TOKEN_OUT[3:2]);
wire rcvdToken_setup  = rcvd_isToken && (rx_pid[3:2] == PID_TOKEN_SETUP[3:2]);
wire rcvdToken_sof    = rcvd_isToken && (rx_pid[3:2] == PID_TOKEN_SOF[3:2]);
wire rcvdData_data0 = rcvd_isData && (rx_pid[3:2] == PID_DATA_DATA0[3:2]); // NOTE: bit2 not strictly required
wire rcvdData_data1 = rcvd_isData && (rx_pid[3:2] == PID_DATA_DATA1[3:2]); // NOTE: bit2 not strictly required
wire rcvdHandshake_ack = rcvd_isHandshake && (rx_pid[3:2] == PID_HANDSHAKE_ACK[3:2]);

wire [6:0] rcvd_hostToDevPids = {
  rcvdToken_in,
  rcvdToken_out,
  rcvdToken_setup,
  rcvdToken_sof,
  rcvdData_data0,
  rcvdData_data1,
  rcvdHandshake_ack};

// Assertions on dev-supported PIDs performed in u_rx.
wire rcvd_supportedPid = |rcvd_hostToDevPids;


wire [1:0] tx_pidCodingGroup = tx_pid[1:0];
wire tx_pidGrp_isToken     = (tx_pidCodingGroup == PIDGROUP_TOKEN); // host-only
wire tx_pidGrp_isData      = (tx_pidCodingGroup == PIDGROUP_DATA);
wire tx_pidGrp_isHandshake = (tx_pidCodingGroup == PIDGROUP_HANDSHAKE);

wire [2:0] tx_pidGrp = {
  tx_pidGrp_isToken,
  tx_pidGrp_isData,
  tx_pidGrp_isHandshake
};
`asrt(tx_pidGrp, i_clk_48MHz, !i_rst, $onehot0(tx_pidGrp))

wire sent_isToken     = tx_accepted && tx_pidGrp_isToken;
wire sent_isData      = tx_accepted && tx_pidGrp_isData;
wire sent_isHandshake = tx_accepted && tx_pidGrp_isHandshake;

// NOTE: Only the non-pidgroup bits are required since sent_* has already
// taken pidgroup bits into consideration.
wire sentData_data0 = sent_isData && (tx_pid[3:2] == PID_DATA_DATA0[3:2]); // NOTE: bit2 not strictly required
wire sentData_data1 = sent_isData && (tx_pid[3:2] == PID_DATA_DATA1[3:2]); // NOTE: bit2 not strictly required
wire sentHandshake_ack = sent_isHandshake && (tx_pid[3:2] == PID_HANDSHAKE_ACK[3:2]);
wire sentHandshake_nak = sent_isHandshake && (tx_pid[3:2] == PID_HANDSHAKE_NAK[3:2]);
wire sentHandshake_stall = sent_isHandshake && (tx_pid[3:2] == PID_HANDSHAKE_STALL[3:2]);

// }}} PID rx/tx decode

// {{{ Transaction type flags

/*
Flags raised on send/receive of SETUP/OUT/IN token indicating start of
transaction, and lowered on end of transaction.
Only one flag may be raised at any time.

During the Setup stage of a Control Transfer, a Setup transaction is used to
transmit information to the control endpoint of a function.
Setup transactions are similar in format to an OUT, but use a SETUP rather than
on OUT PID.

SETUP flag is used by control endpoints to put data into configuration buffer.
*/

wire setupTxn_raise,  setupTxn_lower;
wire outTxn_raise,    outTxn_lower;
wire inTxn_raise,     inTxn_lower;
assign {setupTxn_raise, setupTxn_lower} = {rcvdToken_setup, sentHandshake_ack};
assign {outTxn_raise,   outTxn_lower}   = {rcvdToken_out,   sent_isHandshake};
assign {inTxn_raise,    inTxn_lower}    =
  {rcvdToken_in && !etIsochronous,
   rcvdHandshake_ack || sentHandshake_nak || sentHandshake_stall};

`dff_flag(setupTxn, i_clk_48MHz, i_rst, setupTxn_raise, setupTxn_lower)
`dff_flag(outTxn,   i_clk_48MHz, i_rst, outTxn_raise,   outTxn_lower)
`dff_flag(inTxn,    i_clk_48MHz, i_rst, inTxn_raise,    inTxn_lower)

wire [2:0] txnFlags_d = {
  setupTxn_d,
  outTxn_d,
  inTxn_d
};
`asrt(txnFlag_d, i_clk_48MHz, !i_rst, $onehot0(txnFlags_d))

wire [2:0] txnFlags_q = {
  setupTxn_q,
  outTxn_q,
  inTxn_q
};
`asrt(txnFlag_q, i_clk_48MHz, !i_rst, $onehot0(txnFlags_q))

assign o_txnType = txnFlags_q;

// }}} Transaction type flags

// {{{ addr,endp,frameNumber decode

// Store frameNumber field on each SOF token.
wire updateFrameNumber = rcvdToken_sof;
`dff_cg_srst(reg [10:0], frameNumber, i_clk_48MHz, updateFrameNumber, i_rst, '0)
always @* frameNumber_d = {rx_endp, rx_addr};
assign o_frameNumber = frameNumber_q;

wire addressedToSelf = (rx_addr == i_devAddr);
wire endpSupported = (rx_endp < (inTxn_q ? RX_N_ENDP : TX_N_ENDP));

// Check that transaction is supported and addressed to this device.
// This may be sampled in cycle *after* token is received.
// FSMs for copying buffers should not advance until this, or equivalent logic,
// has been checked.
wire txnSupported = addressedToSelf && endpSupported;

wire rxEndpSelect = rx_endp[$clog2(RX_N_ENDP)-1:0];
wire txEndpSelect = rx_endp[$clog2(TX_N_ENDP)-1:0];

// }}} addr,endp,frameNumber decode

// {{{ Mask/reduce IO per endpoint
/*
Host cannot stall any endpoint so stalling logic is dev-mode only.

Device can send OUT(rx)-STALL handshake to indicate only:
 1. Endpoint is permanently halted.
    Most designs won't have this.

Device can send IN(tx)-STALL handshake to indicate either:
 1. Endpoint is permanently halted.
    Most designs won't have this.
 2. Control transfer not supported.
    All designs will likely have this.
*/

// Endpoint receive
wire [RX_N_ENDP-1:0] erVecMask;
wire [RX_N_ENDP-1:0] erVec_stalled;
wire [RX_N_ENDP-1:0] erVec_isochronous;
generate for (e=0; e < RX_N_ENDP; e=e+1) begin
  localparam STALLABLE = RX_STALLABLE & (1 << e);

  assign erVecMask[e] = addressedToSelf && (e == rx_endp);

  // Mask and reduce i_erStall to detect whether to send IN-STALL handshake.
  assign erVec_stalled[e] = erVecMask[e] && (STALLABLE != 0) && i_erStall[e];

  assign erVec_isochronous[e] = erVecMask[e] && (RX_ISOCHRONOUS & (1 << e));
end endgenerate
`asrt(erVec_stalled, i_clk_48MHz, !i_rst, $onehot0(erVec_stalled))
`asrt(erVec_isochronous, i_clk_48MHz, !i_rst, $onehot0(erVec_isochronous))
wire erStalled = |erVec_stalled;
wire erIsochronous = |erVec_isochronous;
wire erReady = |(i_erReady & erVecMask); // Rx endpoint has space.
wire erValid = |(o_erValid & erVecMask);
wire erRdEn = |(i_erRdEn & erVecMask);
wire [RDIDX_W-1:0] erRdIdx = i_erRdIdx[rxEndpSelect*RDIDX_W +: RDIDX_W];

assign o_erValid = erVecMask & {RX_N_ENDP{rx_acceptData}};

// Endpoint transmit
wire [TX_N_ENDP-1:0] etVecMask;
wire [TX_N_ENDP-1:0] etVec_stalled;
wire [TX_N_ENDP-1:0] etVec_isochronous;
generate for (e=0; e < TX_N_ENDP; e=e+1) begin
  localparam STALLABLE = TX_STALLABLE & (1 << e);

  assign etVecMask[e] = addressedToSelf && (e == rx_endp);

  // Mask and reduce i_etStall to detect whether to signal irrecoverable halting.
  assign etVec_stalled[e] = etVecMask[e] && (STALLABLE != 0) && i_etStall[e];

  assign etVec_isochronous[e] = etVecMask[e] && (TX_ISOCHRONOUS & (1 << e));

  assign o_etTxAccepted[e] = etVecMask[e] && sent_isData;
end endgenerate
`asrt(etVec_stalled, i_clk_48MHz, !i_rst, $onehot0(etVec_stalled))
`asrt(etVec_isochronous, i_clk_48MHz, !i_rst, $onehot0(etVec_isochronous))

wire etStalled = |etVec_stalled;
wire etIsochronous = |etVec_isochronous;
wire etReady = |(o_etReady & etVecMask);
wire etValid = |(i_etValid & etVecMask); // Tx endpoint has data.
wire etWrEn = |(i_etWrEn & etVecMask);
wire [WRIDX_W-1:0] etWrIdx = i_etWrIdx[txEndpSelect*WRIDX_W +: WRIDX_W];
wire [7:0] etWrByte = i_etWrByte[txEndpSelect*8 +: 8];

// }}} Mask/reduce IO per endpoint

// {{{ Stop-and-Wait Automatic Repeat Request

/* 8.6 Data Toggle Synchronization and Retry
USB provides a mechanism to guarantee data sequence synchronization between
data transmitter and receiver across multiple transactions.
This mechanism provides a means of guaranteeing that the handshake phase of a
transaction was interpreted correctly by both the transmitter and receiver.
Synchronization is achieved via use of the DATA0 and DATA1 PIDs and separate
data toggle sequence bits for the data transmitter and receiver.
Receiver sequence bits toggle only when the receiver is able to accept data and
receives an error free data packet with the correct data PID.
Transmitter sequence bits toggle only when the data transmitter receives a
valid ACK handshake.
The data transmitter and receiver must have their sequence bits synchronized at
the start of a transaction.
The synchronization mechanism used varies with the transaction type.
Data toggle synchronization is not supported for ISO transfers.

The two packet types DATA0,DATA1 provide the 1b sequence number required by
stop-and-wait ARQ.

8.6.1 Initialization via SETUP Token
Control transfers use the SETUP token for initializing host and function
sequence bits.
Figure 8-15 shows the host issuing a SETUP packet to a function followed by an
OUT.
The numbers in the circles represent the transmitter and receiver sequence bits.
The function must accept the data and ACK the transaction.
When the function accepts the transaction, it must reset its sequence bit so
that both the host's and function's sequence bits are equal to 1 at the end of
the SETUP transaction.

Each endpoint maintains its own ARQ state.
*/

// DATAx PID to send, per endpoint.
`dff_nocg_srst(reg [TX_N_ENDP-1:0], etArq, i_clk_48MHz, i_rst, '0)
generate for (e=0; e < TX_N_ENDP; e=e+1) begin
  always @*
    if (rcvdToken_setup && etVecMask[e])
      etArq_d[e] = 1'b1;
    else if (awaitHandshake_q && rcvdHandshake_ack && etVecMask[e])
      etArq_d[e] = !etArq_q[e];
    else
      etArq_d[e] = etArq_q[e];
end endgenerate
wire etArq = |(etArq_q & etVecMask);
wire [3:0] tx_nextDataPid = etArq ? PID_DATA_DATA1 : PID_DATA_DATA0;


// Expected DATAx PID to receive, per endpoint.
`dff_nocg_srst(reg [RX_N_ENDP-1:0], erArq, i_clk_48MHz, i_rst, '0)
generate for (e=0; e < RX_N_ENDP; e=e+1) begin
  always @*
    if (rcvdToken_setup && erVecMask[e])
      erArq_d[e] = 1'b0;
    else if (sentHandshake_ack && erVecMask[e])
      erArq_d[e] = !erArq_q[e];
    else
      erArq_d[e] = erArq_q[e];
end endgenerate
wire erArq = |(erArq_q & erVecMask);
wire rx_acceptData = erArq ? rcvdData_data1 : rcvdData_data0;

wire arqMismatch = rcvd_isData && !rx_acceptData; // debug-only
`asrt(arqMismatch, i_clk_48MHz, !i_rst, !arqMismatch)

// }}} Stop-and-Wait Automatic Repeat Request

// {{{ Waiting to receive packet from other end
wire awaitToken_raise,      awaitToken_lower;
wire awaitData_raise,       awaitData_lower;
wire awaitHandshake_raise,  awaitHandshake_lower;

wire awaitToken; // Dev-mode awaitToken flag resets high.
`dff_flag(awaitData,      i_clk_48MHz, i_rst, awaitData_raise,      awaitData_lower)
`dff_flag(awaitHandshake, i_clk_48MHz, i_rst, awaitHandshake_raise, awaitHandshake_lower)

assign {awaitToken_raise, awaitToken_lower} =
  {rcvd_isHandshake ||
   (sent_isData && etIsochronous) ||
   updateFrameNumber,

   rcvd_isToken && !rcvdToken_sof};

`dff_nocg_norst(reg, awaitToken, i_clk_48MHz)
always @*
  if (awaitToken_lower)
    awaitToken_d = 1'b0;
  else if (i_rst || awaitToken_raise)
    awaitToken_d = 1'b1;
  else
    awaitToken_d = awaitToken_q;
assign awaitToken = awaitToken_q;

assign {awaitData_raise, awaitData_lower} =
  {rcvdToken_out || rcvdToken_setup, rcvd_isData || updateFrameNumber};

assign {awaitHandshake_raise, awaitHandshake_lower} =
  {sent_isData && !etIsochronous, rcvd_isHandshake || updateFrameNumber};

wire [2:0] awaitFlags_q = {
  awaitToken,
  awaitData_q,
  awaitHandshake_q
};

`asrt(awaitFlags_q, i_clk_48MHz, !i_rst, $onehot0(awaitFlags_q))

wire await = awaitToken || awaitData_q || awaitHandshake_q;

// }}} Waiting to receive packet from other end

// {{{ Waiting to send packet to other end
/*
A device response PID can be chosen as soon as a packet is received from the host.
USB device can only send these PIDs:
   1. handshake[STALL] - Response to token[IN], token[OUT], data[DATA*]
   2. handshake[NAK] - Response to token[IN], data[DATA*]
   3. handshake[ACK] - Response to data[DATA*]
   4. data[DATA*] - Response to token[IN]
USB device can only receive these PIDs:
   1. token[SOF] - Start-of-Frame. Requires no response.
   2. token[SETUP] - Followed by data[DATA0]. Requires no response.
   3. token[OUT] - Followed by data[DATA*]. Requires no response.
   4. token[IN] - Respond with data[DATA*].
   5. data[DATA*] - After to token[SETUP], token[OUT]. Respond with handshake.
   6. handshake[ACK] - Response to data[DATA*]. Requires no response.
*/

wire tosendRaise_ack;
wire tosendRaise_nak;
wire tosendRaise_stall;
wire tosendRaise_data;
wire [3:0] tosendRaiseVec = {
  tosendRaise_ack,
  tosendRaise_nak,
  tosendRaise_stall,
  tosendRaise_data};
wire tosendRaise = |tosendRaiseVec;
`asrt(tosendRaise, i_clk_48MHz, !i_rst, $onehot0(tosendRaiseVec))

// Wait for SOF to be sent with higher priority, or cancel transaction which
// goes over frame boundary.
wire tosendLower = (tx_accepted && !tosendRaise) || updateFrameNumber;
`dff_flag(tosend, i_clk_48MHz, i_rst, tosendRaise, tosendLower)

assign tosendRaise_data = rcvdToken_in && !etStalled && etValid;

assign tosendRaise_stall = (
    rcvd_isData &&              // Got a data packet,
    (setupTxn_q || outTxn_q) && //   which was expected,
    !erIsochronous &&           //   this endpoint does handshake,
    erStalled                   //   but is irrecoverably halted.
  ) || (
    rcvdToken_in &&         // Got token[IN],
    !etIsochronous &&       //   this endpoint does handshake,
    etStalled               //   but is irrecoverably halted.
  );

assign tosendRaise_nak = (
    rcvd_isData &&              // Got a data packet,
    (setupTxn_q || outTxn_q) && //   which was expected,
    !erIsochronous &&           //   this endpoint does handshake,
    !erStalled &&               //   this endpoint is not irrecoverably halted,
    !erReady                    //   but endpoint has no space to receive.
  ) || (
    rcvdToken_in &&   // Got token[IN],
    !etStalled &&     //   and endpoint could send data eventually,
    !etValid          //   but doesn't have data yet.
  );

assign tosendRaise_ack =
  rcvd_isData &&              // Got a data packet,
  (setupTxn_q || outTxn_q) && //   which was expected,
  !erIsochronous &&           //   this endpoint does handshake,
  !erStalled &&               //   this endpoint is not irrecoverably halted,
  (erReady || !rx_acceptData);//   and endpoint does have space to receive,
                              //     or data is discarded by ARQ mismatch.

// }}} Waiting to send packet to other end

// NOTE: The txn*_q, await*_q, tosend_q flags act as a FSM where assertions
// place restrictions on valid states, but the overall state is easily reasoned
// about.

`dff_cg_norst(reg [3:0], tosendPid, i_clk_48MHz, tosendRaise)
always @*
   case (tosendRaiseVec[3:1])
    3'b100:   tosendPid_d = PID_HANDSHAKE_ACK;
    3'b010:   tosendPid_d = PID_HANDSHAKE_NAK;
    3'b001:   tosendPid_d = PID_HANDSHAKE_STALL;
    default:  tosendPid_d = tx_nextDataPid;
  endcase

assign tx_valid = tosend_q;
assign tx_pid = tosendPid_q;

// Endpoint should be holding data and valid steady, waiting for o_etReady to go
// high to accept it.
// Data will be sent before being accepted from endpoint.
// Endpoint will only know data has been sent when an ACK has been received.
assign o_etReady = etVecMask & {TX_N_ENDP{(rcvdHandshake_ack)}};

endmodule
