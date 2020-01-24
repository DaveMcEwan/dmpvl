`include "dff.vh"

// The OUT Protocol Engine receives data from the host.
module usbPeOut #(
  parameter N_EP_OUT = 1,
  parameter MAX_OUT_PACKET_SIZE = 8 // Must be in {8,16,32}
) (
  input  wire                   i_clk,
  input  wire                   i_rst,

  input  wire [6:0]             i_devAddr,

  // Endpoint interface
  output wire [N_EP_OUT-1:0]    o_outEp_dataAvail,
  input  wire [N_EP_OUT-1:0]    i_outEp_dataGet,
  output wire [7:0]             o_outEp_data,
  input  wire [N_EP_OUT-1:0]    i_outEp_grant,

  output wire [N_EP_OUT-1:0]    o_outEp_setup, // Last token was SETUP.
  output wire [N_EP_OUT-1:0]    o_outEp_acked, // Pulse high when ACK is sent.

  input  wire                   i_rxPktBegin,
  input  wire                   i_rxPktEnd,
  input  wire                   i_rxPktValid,

  // Most recent packet received.
  input  wire [3:0]             i_rxPid,
  input  wire [6:0]             i_rxAddr,
  input  wire [3:0]             i_rxEndp,
  input  wire [10:0]            i_rxFrameNum,

  // i_rxData is pushed into endpoint controller.
  input  wire                   i_rxDataPut,
  input  wire [7:0]             i_rxData,

  // Strobe to send new packet.
  output wire                   o_txPktBegin,
  input  wire                   i_txPktEnd,
  output wire [3:0]             o_txPid
);

`include "usbSpec.vh"

genvar e;

wire currentEpNotPutting;
wire outXfr_initToWaiting;

wire currentFifoFull;
wire currentFifoEmpty;

`dff_cg_norst(reg [3:0], currentEndp, i_clk, outXfr_initToWaiting)
always @* currentEndp_d = i_rxEndp;

// {{{ Initial packet decode

/* Implementation Notes
usbRxPkt signals the end of a packet sequence being received, by pulsing
rxPktEnd, where the packet may be valid (passed CRC) or invalid (failed CRC).
Decoding whether the packet is valid/invalid and intended for this device is
the first decode step.
usbRxPkt takes care of the CRC, and provides the PID, ADDR, ENDP fields
to this module (usbPeOut) as i_rxPid, i_rxAddr, i_rxEndp.
*/
wire rcvd_pktValid = i_rxPktEnd && i_rxPktValid;
wire rcvd_pktInvalid = i_rxPktEnd && !i_rxPktValid;
wire pktReceived =
  rcvd_pktValid &&            // Received a valid packet,
  (i_rxAddr == i_devAddr) &&  // addressed to this device, (USB device address assigned by host at enumeration)
  (i_rxEndp < N_EP_OUT);   // on a supported endpoint.

/* 8.3.1 Packet Identifier Field
A packet identifier (PID) immediately follows the SYNC field of every USB
packet.
A PID consists of a 4b packet type field.
The PID indicates the type of packet and, by inference, the format of the
packet and the type of error detection applied to the packet.
PIDs are divided into four coding groups: TOKEN, DATA, HANDSHAKE, and SPECIAL,
with the first two transmitted PID bits (PID<1:0>) indicating which group.
*/
wire [1:0] pidCodingGroup = i_rxPid[1:0];

/* 8.4.3 Data Packets
A data packet consists of a PID, a data field, and a CRC as shown in Figure 8-7.
There are two types of data packets, identified by differing PIDs: DATA0 and
DATA1.
Two data packet PIDs are defined to support data toggle synchronization
(refer to Section 8.6).

    8b      0..1023B      16b
    PID  |  DATA       |  CRC16

      Figure 8-7. Data Packet Format

Data must always be sent in integral numbers of bytes.
*/
wire rcvd_pidData = rcvd_pktValid && (pidCodingGroup == PIDGROUP_DATA);
wire rcvd_pidNotData = rcvd_pktValid && (pidCodingGroup != PIDGROUP_DATA);

// }}} Initial packet decode

assign outXfr_initToWaiting =
  (outXfr_q == XFR_INIT) &&
  (rcvd_pidTokenOUT || rcvd_pidTokenSETUP);

// {{{ outEp_setup

/* 8.4.1 Token Packets
Figure 8-5 shows the field formats for a token packet.
A token consists of a PID, specifying either IN, OUT, or SETUP packet type,
and ADDR and ENDP fields.
For OUT and SETUP transactions, the address and endpoint fields uniquely
identify the endpoint that will receive the subsequent data packet.
For IN transactions, these fields uniquely identify which endpoint should
transmit a data packet.
Only the host can issue token packets.
IN PIDs define a data transaction from a function to the host.
OUT and SETUP PIDs define data transactions from the host to a function.

    8b      7b       4b       5b
    PID  |  ADDR  |  ENDP  |  CRC5

      Figure 8-5 Token Format

Implementation Notes
Tokens are used by the FSMs for endpoints so some decode is performed here,
providing a flag per endpoint, o_outEp_setup, which is raised when a SETUP
token is received, and lowered when an OUT token is received.
Control endpoints can use this to put their FSMs into the correct state.
*/
wire rcvd_pidTokenOUT = pktReceived && (i_rxPid == PID_TOKEN_OUT);
wire rcvd_pidTokenSETUP = pktReceived && (i_rxPid == PID_TOKEN_SETUP);

`dff_nocg_srst(reg [N_EP_OUT-1:0], outEp_setup, i_clk, i_rst, 'd0)

generate for (e=0; e < N_EP_OUT; e=e+1) begin
  always @*
    if ((i_rxEndp == e) && rcvd_pidTokenSETUP)
      outEp_setup_d[e] = 1'b1;
    else if ((i_rxEndp == e) && rcvd_pidTokenOUT)
      outEp_setup_d[e] = 1'b0;
    else
      outEp_setup_d[e] = outEp_setup_q[e];
end endgenerate

assign o_outEp_setup = outEp_setup_q;

// }}} outEp_setup

// {{{ Sequence bit

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

8.6.1 Initialization via SETUP Token
Control transfers use the SETUP token for initializing host and function
sequence bits.
The function must accept the data and ACK the transaction.
When the function accepts the transaction, it must reset its sequence bit so
that both the host’s and function’s sequence bits are equal to 1 at the end of
the SETUP transaction.

8.6.2 Successful Data Transactions
For the data transmitter, this means that it toggles its sequence bit upon
receipt of an ACK.
The receiver toggles its sequence bit only if it receives a valid data packet
and the packet’s data PID matches the receiver’s sequence bit.
During each transaction, the receiver compares the transmitter sequence bit
(encoded in the data packet PID as either DATA0 or DATA1) with its receiver
sequence bit.
If data cannot be accepted, the receiver must issue a NAK.
If data can be accepted and the receiver’s sequence bit matches the PID
sequence bit, then data is accepted.
Sequence bits may only change if a data packet is transmitted.
Two-phase transactions in which there is no data packet leave the transmitter
and receiver sequence bits unchanged.
*/
`dff_nocg_srst(reg [N_EP_OUT-1:0], expSeqBit, i_clk, i_rst, 'd0)

generate for (e=0; e < N_EP_OUT; e=e+1) begin
  always @*
    if (rcvd_pidTokenSETUP && (i_rxEndp == e))
      expSeqBit_d[e] = 1'b0;
    else if (o_outEp_acked[e])
      expSeqBit_d[e] = !expSeqBit_q[e];
    else
      expSeqBit_d[e] = expSeqBit_q[e];
end endgenerate

                                                  /* verilator lint_off WIDTH */
wire currentExpSeqBit = expSeqBit_q[i_rxEndp];
                                                  /* verilator lint_on  WIDTH */

/* Top bit of PID holds the actual sequence bit.
PID_DATA_DATA0 = 4'b0011;
PID_DATA_DATA1 = 4'b1011;
*/
wire actSeqBit = i_rxPid[3];

// Assert when actual sequence bit does not match expected.
// This causes the
wire badSeqBit = rcvd_pidData && (actSeqBit != currentExpSeqBit);

// }}} Sequence bit

// {{{ Manage flow handshake packets to usbTxPkt
localparam XFR_INIT        = 4'b0001;
localparam XFR_WAITING     = 4'b0010;
localparam XFR_BEGIN_RX    = 4'b0100;
localparam XFR_ACK_OR_NAK  = 4'b1000;
`dff_nocg_srst(reg [3:0], outXfr, i_clk, i_rst, XFR_INIT)

always @*
  case (outXfr_q)
    XFR_INIT:
      if (rcvd_pidTokenOUT || rcvd_pidTokenSETUP)
        outXfr_d = XFR_WAITING;
      else
        outXfr_d = XFR_INIT;

    XFR_WAITING:
      if (i_rxPktBegin)
        outXfr_d = XFR_BEGIN_RX;
      else
        outXfr_d = XFR_WAITING;

    XFR_BEGIN_RX:
      if (badSeqBit || rcvd_pktInvalid || rcvd_pidNotData)
        outXfr_d = XFR_INIT;        // Don't send ACK/NAK.
      else if (rcvd_pidData)
        outXfr_d = XFR_ACK_OR_NAK;  // ACK/NAK each data packet.
      else
        outXfr_d = XFR_BEGIN_RX;

    XFR_ACK_OR_NAK:           // Single cycle state sends NAK using
      outXfr_d = XFR_INIT;    // o_txPktBegin and o_txPid.

    default:
      outXfr_d = XFR_INIT;
  endcase

// Set when the endpoint buffer is unable to receive the out transfer.
`dff_nocg_norst(reg, nakOutTransfer, i_clk)
always @*
  if (outXfr_q == XFR_WAITING)
    nakOutTransfer_d = currentEpNotPutting;
  else
    nakOutTransfer_d = nakOutTransfer_q;

/* A packet is sent to usbTxPkt by pulsing o_txPktBegin.
This block (usbPeOut) only sends handshake packets to the host so no data
is required, and the PID options are limited to STALL, NAK, ACK.
*/
assign o_txPktBegin =
  ((outXfr_q == XFR_BEGIN_RX) && badSeqBit) || // Retry transmitting handshake packet.
  (outXfr_q == XFR_ACK_OR_NAK);                // Received all data, send a handshake.

reg [3:0] txPid;
always @*
  if ((outXfr_q == XFR_ACK_OR_NAK) && nakOutTransfer_q)
    txPid = PID_HANDSHAKE_NAK;
  else
    txPid = PID_HANDSHAKE_ACK;

assign o_txPid = txPid;

// }}} Manage flow handshake packets to usbTxPkt

/* Pulse o_outEp_acked when an ACK is sent.
Control endpoints can use this to advance their FSMs.
*/
generate for (e=0; e < N_EP_OUT; e=e+1) begin
  assign o_outEp_acked[e] =
    (e == currentEndp_q) &&
    !nakOutTransfer_q &&
    (outXfr_q == XFR_ACK_OR_NAK);
end endgenerate

wire rollbackBadData =
  (outXfr_q == XFR_BEGIN_RX) &&
  (badSeqBit || rcvd_pktInvalid || rcvd_pidNotData);

wire rollbackNak =
  (outXfr_q == XFR_ACK_OR_NAK) &&
  nakOutTransfer_q;


// Use the bus grant line to determine the outEpNum (where the data is)
// priority encoder from onehot i_outEp_grant.
integer j;
reg [3:0] outEpNum;
always @* begin
  outEpNum = 0;
  for (j=0; j < N_EP_OUT; j=j+1) begin
    if (i_outEp_grant[j])
      outEpNum = j[3:0]; // Explicit width for lint.
  end
end


// Endpoint FSM manages one large buffer shared between all endpoints.
localparam EP_READY   = 3'b001;
localparam EP_PUTTING = 3'b010;
localparam EP_GETTING = 3'b100;
(* mem2reg *) reg [2:0] epFsm_q [N_EP_OUT]; // dff_nocg_srst
(* mem2reg *) reg [2:0] epFsm_d [N_EP_OUT];

// Address registers - one bit longer than required to permit fullness != emptyness
localparam LOG2_PKTSIZE = $clog2(MAX_OUT_PACKET_SIZE);
(* mem2reg *) reg [LOG2_PKTSIZE:0] epGetAddr_q [N_EP_OUT]; // dff_nocg_norst
(* mem2reg *) reg [LOG2_PKTSIZE:0] epGetAddr_d [N_EP_OUT];
(* mem2reg *) reg [LOG2_PKTSIZE:0] epPutAddr_q [N_EP_OUT]; // dff_nocg_srst
(* mem2reg *) reg [LOG2_PKTSIZE:0] epPutAddr_d [N_EP_OUT];

                                                  /* verilator lint_off WIDTH */
wire currentEpFull = epPutAddr_q[currentEndp_q][LOG2_PKTSIZE];

wire [2:0] currentEpFsm = epFsm_q[currentEndp_q];

wire [4+LOG2_PKTSIZE-1:0] bufferPutAddr =
  {currentEndp_q, epPutAddr_q[currentEndp_q][LOG2_PKTSIZE-1:0]};

wire [4+LOG2_PKTSIZE-1:0] bufferGetAddr =
  {outEpNum, epGetAddr_q[outEpNum][LOG2_PKTSIZE-1:0]};
                                                  /* verilator lint_on  WIDTH */

assign currentEpNotPutting = (currentEpFsm != EP_PUTTING);

wire bufferDoWrite =
  (outXfr_q == XFR_BEGIN_RX) &&
  !nakOutTransfer_q &&
  i_rxDataPut &&
  !currentEpFull;

// TODO Replace with flushable FIFOs, read and write always in order.
reg [7:0] buffer_m [MAX_OUT_PACKET_SIZE * N_EP_OUT]; // memory
always @(posedge i_clk) // memory
  if (bufferDoWrite)
                                                  /* verilator lint_off WIDTH */
    buffer_m[bufferPutAddr] <= i_rxData;
                                                  /* verilator lint_on  WIDTH */

`dff_nocg_norst(reg [7:0], outEp_data, i_clk)
                                                  /* verilator lint_off WIDTH */
always @* outEp_data_d = buffer_m[bufferGetAddr];
                                                  /* verilator lint_on  WIDTH */
assign o_outEp_data = outEp_data_q;


generate for (e=0; e < N_EP_OUT; e=e+1) begin

  always @*
    case (epFsm_q[e])
      EP_READY:
        if (outXfr_initToWaiting && (i_rxEndp == e))
          epFsm_d[e] = EP_PUTTING;
        else
          epFsm_d[e] = epFsm_q[e];

      EP_PUTTING: // Data transfer from host, via usbRxPkt, into buffer.
        if (o_outEp_acked[e])
          epFsm_d[e] = EP_GETTING;
        else if ((rollbackBadData || rollbackNak) && (currentEndp_q == e))
          epFsm_d[e] = EP_READY;
        else
          epFsm_d[e] = epFsm_q[e];

      EP_GETTING: // Consumer must take data from buffer.
        if (!o_outEp_dataAvail[e])
          epFsm_d[e] = EP_READY;
        else
          epFsm_d[e] = epFsm_q[e];

      default:
        epFsm_d[e] = EP_READY;
    endcase


  always @*
    if (epFsm_d[e] == EP_READY)
      epGetAddr_d[e] = '0;
    else if ((epFsm_d[e] == EP_GETTING) && i_outEp_dataGet[e])
      epGetAddr_d[e] = epGetAddr_q[e] + 'd1;
    else
      epGetAddr_d[e] = epGetAddr_q[e];

  always @*
    if ((outXfr_q == XFR_WAITING) && !currentEpNotPutting)
      epPutAddr_d[e] = '0;
    else if ((outXfr_q == XFR_BEGIN_RX) &&
             !nakOutTransfer_q &&
             i_rxDataPut &&
             (currentEndp_q == e))
      epPutAddr_d[e] = epPutAddr_q[e] + 'd1;
    else
      epPutAddr_d[e] = epPutAddr_q[e];


  always @(posedge i_clk) // dff_nocg_srst
    if (i_rst)
      epFsm_q[e] = EP_READY;
    else
      epFsm_q[e] = epFsm_d[e];

  always @(posedge i_clk) // dff_nocg_norst
    epGetAddr_q[e] <= epGetAddr_d[e];

  always @(posedge i_clk) // dff_nocg_srst
    if (i_rst)
      epPutAddr_q[e] <= '0;
    else
      epPutAddr_q[e] <= epPutAddr_d[e];


  assign o_outEp_dataAvail[e] =
                                                  /* verilator lint_off WIDTH */
          // 2'd2 is intentionally too small to force yosys to zero-extend
          // without size casting.
    (epGetAddr_q[e] < (epPutAddr_q[e] - 2'd2)) &&
                                                  /* verilator lint_on  WIDTH */
    (epFsm_q[e] == EP_GETTING);

end endgenerate


endmodule
