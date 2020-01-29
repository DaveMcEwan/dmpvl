`include "asrt.vh"
`include "dff.vh"

module usbfsPktTx #(
  parameter AS_HOST_NOT_DEV = 1, // 1=Operate as host, 0=Operate as device/function.
  parameter MAX_PKT = 8  // in {8,16,32,64}. wMaxPacketSize
) (
  input  wire                       i_clk_12MHz, // May jitter slightly.
  input  wire                       i_rst,

  // Valid/ready pipeline interface/handshake.
  // NOTE: Where PID does not require a data payload, i_data[...:11] and
  // i_data_nBytes are ignored.
  // Where PID is a token the bottom 11 bits of i_data are used for address,
  // endpoint, and frame number, with no consideration of i_data_nBytes.
  output wire                       o_ready,
  input  wire                       i_valid,

  output wire                       o_eopDone,

  input  wire [3:0]                 i_pid,
  input  wire [8*MAX_PKT-1:0]       i_data,
  input  wire [$clog2(MAX_PKT):0]   i_data_nBytes,

  // USB {d+, d-}
  output wire                       o_dp,
  output wire                       o_dn,

  output wire                       o_inflight
);
// NOTE: A design/implementation based on this logic uses approximately 60 DFFs,
// assuming that the data source is external.

`include "usbSpec.vh"

// NOTE: Packet will begin sending with SYNC_SOP in cycle following this.
wire drv_accepted = o_ready && i_valid;

// Delayed version just for driver assumptions.
`dff_nocg_srst(reg, drv_accepted, i_clk_12MHz, i_rst, 1'b0)
always @* drv_accepted_d = drv_accepted;

// Accept and store inputs.
`dff_cg_norst_d(reg [$clog2(MAX_PKT):0], data_nBytes, i_clk_12MHz, drv_accepted, i_data_nBytes)
`dff_cg_norst_d(reg [3:0], pid, i_clk_12MHz, drv_accepted, i_pid)
`dff_cg_norst_d(reg [8*MAX_PKT-1:0], data, i_clk_12MHz, drv_accepted, i_data)

// {{{ PID sanity check

wire [1:0] pidCodingGroup = pid_q[1:0];
wire pidGrp_isToken     = (pidCodingGroup == PIDGROUP_TOKEN);
wire pidGrp_isData      = (pidCodingGroup == PIDGROUP_DATA);
wire pidGrp_isHandshake = (pidCodingGroup == PIDGROUP_HANDSHAKE);
wire pidGrp_isSpecial   = (pidCodingGroup == PIDGROUP_SPECIAL);

`asrt(token_nBytes, i_clk_12MHz, !i_rst && drv_accepted_q && pidGrp_isToken, (data_nBytes_q == 'd2))

// NOTE: Data packets with zero bytes are allowed, for example to finish
// a Control Transfer.
//`asrt(data_nBytes, i_clk_12MHz, !i_rst && drv_accepted_q && pidGrp_isData, (data_nBytes_q > 'd0))

// NOTE: Design/implementation doesn't require all 4 PID bits to be stored for
// the duration of the packet, only the coding group.

// A token consists of a PID, specifying either IN, OUT, or SETUP packet type,
// and ADDR and ENDP fields.
// For OUT and SETUP transactions, the address and endpoint fields uniquely
// identify the endpoint that will receive the subsequent data packet.
// For IN transactions, these fields uniquely identify which endpoint should
// transmit a data packet.
// *Only the host can issue token packets.*
// IN PIDs define a data transaction dev->host.
// OUT and SETUP PIDs define data transactions host->dev.
wire pid_isTokenIn    = (pid_q == PID_TOKEN_IN);
wire pid_isTokenOut   = (pid_q == PID_TOKEN_OUT);
wire pid_isTokenSetup = (pid_q == PID_TOKEN_SETUP);

// Start of Frame (SOF) packets are issued by the host at a nominal rate of once
// every 1ms ±0.05.
// Frame timing sensitive devices, which do not need to keep track of frame
// number, need only decode the SOF PID; they can ignore the frame number and
// its CRC.
// If a device needs to track frame number, it must comprehend both the PID
// and the time stamp.
wire pid_isTokenSof   = (pid_q == PID_TOKEN_SOF);

// There are two types of data packets, identified by differing PIDs.
// Two data packet PIDs are defined to support data toggle synchronization.
// Data must always be sent in integral numbers of bytes.
wire pid_isData0 = (pid_q == PID_DATA_DATA0);
wire pid_isData1 = (pid_q == PID_DATA_DATA1);

// ACK indicates that the data packet was received without bit stuff or CRC
// errors over the data field and that the data PID was received correctly.
// ACK may be issued either when sequence bits match and the receiver can accept
// data or when sequence bits mismatch and the sender and receiver must
// resynchronize to each other.
// An ACK handshake is applicable only in transactions in which data has been
// transmitted and where a handshake is expected.
// ACK can be returned by the host for IN transactions and by a device for OUT
// transactions.
wire pid_isHandshakeAck   = (pid_q == PID_HANDSHAKE_ACK);

// NAK indicates that a device was unable to accept data from the host (OUT)
// or that a device has no data to transmit to the host (IN).
// NAK can only be returned by devices in the data phase of IN transactions or
// the handshake phase of OUT transactions.
// *The host can never issue a NAK.*
// NAK is used for flow control purposes to indicate that a device is
// temporarily unable to transmit or receive data, but will eventually be able
// to do so without need of host intervention.
// NAK is also used by interrupt endpoints to indicate that no interrupt is
// pending.
wire pid_isHandshakeNak = (pid_q == PID_HANDSHAKE_NAK);

// STALL is returned by a device in response to an IN token or after the data
// phase of an OUT.
// STALL indicates that a device is unable to transmit or receive data, and
// that the condition requires host intervention to remove the stall.
// Once a device’s endpoint is stalled, the device must continue returning STALL
// until the condition causing the stall has been cleared through host
// intervention.
// *The host is not permitted to return a STALL under any condition.*
wire pid_isHandshakeStall = (pid_q == PID_HANDSHAKE_STALL);

// USB supports signaling at two speeds: full speed signaling at 12.0 Mbs and
// low speed signaling at 1.5 Mbps.
// Hubs disable downstream bus traffic to all ports to which low speed devices
// are attached during full speed downstream signaling.
// This is required both for EMI reasons and to prevent any possibility that a
// low speed device might misinterpret downstream a full speed packet as being
// addressed to it.
// All downstream packets transmitted to low speed devices require a preamble.
// The preamble consists of a SOP followed by a PID, both sent at full speed.
// Hubs must comprehend the PRE PID; all other USB devices must ignore it and
// treat it as undefined.
// After the end of the preamble PID, the host must wait at least four full
// speed bit times during which hubs must complete the process of configuring
// their repeater sections to accept low speed signaling.
// During this hub setup interval, hubs must drive their full speed and low
// speed ports to their respective idle states.
// Hubs must be ready to accept low speed signaling from the host before the
// end of the hub setup interval.
// NOTE: This PID is not supported by this driver as I have no current need for
// hub logic.
wire pid_isSpecialPre = (pid_q == PID_SPECIAL_PRE);

`ifndef SYNTHESIS
wire [6:0] hostToDevPids = {
  pid_isTokenIn,
  pid_isTokenOut,
  pid_isTokenSetup,
  pid_isTokenSof,
  pid_isData0,
  pid_isData1,
  pid_isHandshakeAck};

wire [4:0] devToHostPids = {
  pid_isData0,
  pid_isData1,
  pid_isHandshakeAck,
  pid_isHandshakeNak,
  pid_isHandshakeStall};

wire pid_type_onehot;
generate if (AS_HOST_NOT_DEV != 0) begin
  assign pid_type_onehot = $onehot(hostToDevPids);
end else begin
  assign pid_type_onehot = $onehot(devToHostPids);
end endgenerate

// Assume requests have sane values for i_pid.
`asrt(pid_type_onehot, i_clk_12MHz, !i_rst && drv_accepted_q, pid_type_onehot)
`endif

// }}} PID sanity check

// {{{ Count bits and bytes.
// approx 7 dff with minimal MAX_PKT

`dff_nocg_srst(reg [2:0], bitCntr, i_clk_12MHz, i_rst || o_eopDone, '0)
always @*
  if (!doStuff && inflight_q)
    bitCntr_d = bitCntr_q + 1;
  else
    bitCntr_d = bitCntr_q;

wire byteSent = (bitCntr_q == '1) && inflight_q && !doStuff;

// Max number of bytes in a packet is (1<SOP> + 1<PID> + MAX_PKT + 2<CRC16>)
// SOP is always sent when (nBytesSent_q == 0).
// PID is always sent when (nBytesSent_q == 1).
// Token fields byte0 is always sent when (nBytesSent_q == 2).
// Token fields byte1 (with crc5) is always sent when (nBytesSent_q == 3).
`dff_nocg_srst(reg [$clog2(MAX_PKT):0], nBytesSent, i_clk_12MHz, drv_accepted, '0)
always @*
  if (byteSent)
    nBytesSent_d = nBytesSent_q + 1;
  else
    nBytesSent_d = nBytesSent_q;

wire [$clog2(MAX_PKT):0] nBytesPkt_handshake = 'd2; // SOP, PID
wire [$clog2(MAX_PKT):0] nBytesPkt_token = 'd4; // SOP, PID, TOKFIELD, TOKFIELD
wire [$clog2(MAX_PKT):0] nBytesPkt_data = data_nBytes_q + 'd4; // SOP, PID, data1..N, CRC, CRC
`asrt(nBytesSent_handshake, i_clk_12MHz, !i_rst && o_eopDone && pidGrp_isHandshake, (nBytesSent_q == nBytesPkt_handshake))
`asrt(nBytesSent_token,     i_clk_12MHz, !i_rst && o_eopDone && pidGrp_isToken,     (nBytesSent_q == nBytesPkt_token))
`asrt(nBytesSent_data,      i_clk_12MHz, !i_rst && o_eopDone && pidGrp_isData,      (nBytesSent_q == nBytesPkt_data))

// }}} Count bits and bytes.

// {{{ Display accepted packet
`ifndef SYNTHESIS

wire [6:0] tokenAddr = data_q[6:0];
wire [3:0] tokenEndp = data_q[10:7];
wire [10:0] tokenFrameNumber = data_q[10:0];

always @(posedge i_clk_12MHz) if (drv_accepted_q) begin : info
  string s_pidName;
  string s_pid;
  string s_data;

  if (pid_isTokenIn)
    $sformat(s_pidName, "Token[IN]");
  else if (pid_isTokenOut)
    $sformat(s_pidName, "Token[OUT]");
  else if (pid_isTokenSetup)
    $sformat(s_pidName, "Token[SETUP]");
  else if (pid_isTokenSof)
    $sformat(s_pidName, "Token[SOF]");
  else if (pid_isData0)
    $sformat(s_pidName, "Data[DATA0]");
  else if (pid_isData1)
    $sformat(s_pidName, "Data[DATA1]");
  else if (pid_isHandshakeAck)
    $sformat(s_pidName, "Handshake[ACK]");
  else if (pid_isHandshakeNak)
    $sformat(s_pidName, "Handshake[NAK]");
  else if (pid_isHandshakeStall)
    $sformat(s_pidName, "Handshake[STALL]");
  else
    $sformat(s_pidName, "UNKNOWN");

  $sformat(s_pid, "pid=%h=%s", pid_q, s_pidName);

  if (pidGrp_isData)
    $sformat(s_data, " data=0x%0h, nBytes=%0d", data_q, data_nBytes_q);
  else if (pid_isTokenSof)
    $sformat(s_data, " frameNumber=%0d", tokenFrameNumber);
  else if (pidGrp_isToken)
    $sformat(s_data, " addr=%0d, endp=%0d", tokenAddr, tokenEndp);
  else if (pidGrp_isHandshake)
    $sformat(s_data, "");
  else
    $sformat(s_data, " UNKNOWN PIDGRP");

  $display("INFO:t%0t:%m: Sending %s%s ...", $time, s_pid, s_data);
end : info

`endif
// }}} Display accepted packet

// {{{ Stabilize 1B of non-CRC data to serialize.
// approx 8 dff

// Packet field formats:
//                             LSB                               MSB
// 8.4.4 Handshake              {PID:8b}
// 8.4.1 Token IN/OUT/SETUP     {PID:8b, ADDR:7b, ENDP:4b, CRC5:5b}
// 8.4.1 Token SOF              {PID:8b, FRAMENUMBER:11b, CRC5:5b}
// 8.4.2 Data                   {PID:8b, DATA:0..64B, CRC16:16b}
// A data packet consists of the PID followed by 0..1024B of data payload (up to
// 1024B for high-speed devices, 64B for full-speed devices, and at most 8B for
// low-speed devices), and the 16b CRC.

// NOTE: Design/implementation can use similar logic, but take data from a fifo
// or something else with block RAMs.
wire dataAvailable = (nBytesSent_d < (data_nBytes_q + 'd2)); // SOP, PID, data...
wire [7:0] dataByte = data_q[8*(nBytesSent_q) +: 8]; // Like the head of a fifo.

// Packet size is always an integer number of bytes.
// i_pid, i_data (includes ADDR, ENDP fields).
`dff_nocg_norst(reg [7:0], nextByte, i_clk_12MHz)
always @*
  if (drv_accepted)
    nextByte_d = {~i_pid, i_pid}; // 8.3.1 Packet Identifier Field
  else if (byteSent)
    nextByte_d = dataByte;
  else
    nextByte_d = nextByte_q;

// }}} Stabilize 1B of non-CRC data to serialize.

// Mini state machine for sequencing CRC[0], CRC[1], EOP.
// approx 3 dff
wire isLastDataByte = ((data_nBytes_q + 'd1) == nBytesSent_q);
`dff_nocg_srst(reg [2:0], lastDataBytes, i_clk_12MHz, i_rst, '0)
always @*
  if (drv_accepted)
    lastDataBytes_d = '0;
  else if (byteSent)
    lastDataBytes_d = {lastDataBytes_q[1:0], isLastDataByte};
  else
    lastDataBytes_d = lastDataBytes_q;

// {{{ Calculate CRCs.
// approx 21 dff

// A seed value of '1 is used to allow leading zeros to be CRC protected.
// The result is inverted otherwise trailing zeros could not be detected as
// errors.

wire doDataCrc =
  !doStuff &&
  (nBytesSent_q >= 'd2) &&
  (lastDataBytes_q == '0);

// 8.3.5.2 Data CRCs
// G(x) = x^16 + x^15 + x^2 + 1
`dff_nocg_norst(reg [15:0], crc16, i_clk_12MHz)
wire crc16Loop = currentBit ^ crc16_q[0];
always @*
  if (drv_accepted)
    crc16_d = '1;
  else if (lastDataBytes_q[0] && !doStuff)
    crc16_d = crc16_q >> 1; // Shift after first CRC byte sent.
  else if (doDataCrc)
    crc16_d = {crc16Loop,
               crc16_q[15],
               crc16_q[14] ^ crc16Loop,
               crc16_q[13],
               crc16_q[12],
               crc16_q[11],
               crc16_q[10],
               crc16_q[9],
               crc16_q[8],
               crc16_q[7],
               crc16_q[6],
               crc16_q[5],
               crc16_q[4],
               crc16_q[3],
               crc16_q[2],
               crc16_q[1] ^ crc16Loop};
  else
    crc16_d = crc16_q;

wire doTokenCrc =
  !doStuff &&
  ((nBytesSent_q == 'd2) ||                        // ADDR:7b,ENDP:1b
   ((nBytesSent_q == 'd3) && (bitCntr_q < 3'd3))); // ENDP:3b

// 8.3.5.1 Token CRC
// G(x) = x^5 + x^2 + 1
`dff_nocg_norst(reg [4:0], crc5, i_clk_12MHz)
wire crc5Loop = currentBit ^ crc5_q[0];
always @*
  if (drv_accepted)
    crc5_d = '1;
  else if (doTokenCrc)
    crc5_d = {crc5Loop, crc5_q[4], crc5_q[3] ^ crc5Loop, crc5_q[2], crc5_q[1]};
  else
    crc5_d = crc5_q;

// }}} Calculate CRCs.

// {{{ Mux data into 8b shift register.
// approx 8 dff

wire takeCrc5;
generate if (AS_HOST_NOT_DEV) begin
  assign takeCrc5 =
    pidGrp_isToken &&
    (nBytesSent_q == 'd3) &&
    (bitCntr_q == 3'd2);
end else begin
  assign takeCrc5 = 1'b0;
end endgenerate

wire takeCrc16 =
  pidGrp_isData &&
  (lastDataBytes_d != '0) &&
  byteSent;

// Bit to send is always the LSB of this.
`dff_cg_srst(reg [7:0], byteShift, i_clk_12MHz, !doStuff, drv_accepted, SYNC_SOP)
always @*
  if (takeCrc5) // NOTE: Branch only taken in host mode.
    byteShift_d = {byteShift_q[7:5], ~crc5_d}; // Only bottom 5 update.
  else if (takeCrc16)
    byteShift_d = ~crc16_d[7:0];
  else if (byteSent)
    byteShift_d = nextByte_q;
  else
    byteShift_d = byteShift_q >> 1;

wire currentBit = byteShift_q[0];

// }}} Mux data into 8b shift register.

// {{{ Calculate bit stuffing and mux into sendBit.
// approx 6 dff

// 7.1.6 Bit Stuffing
// The clock is transmitted encoded along with the differential data.
// The clock encoding scheme is NRZI (Non Return to Zero Invert) with bit
// stuffing to ensure adequate transitions.
// Bit stuffing is enabled beginning with the SYNC_SOP and throughout the
// entire transmission.
// The data “one” that ends the Sync Pattern is counted as the first one in a
// sequence.
// Bit stuffing is always enforced, without exception.
`dff_cg_srst(reg [NRZI_MAXRL_ONES-1:0], nrziHistory, i_clk_12MHz, inflight_q, (drv_accepted || i_rst), '0)
always @* nrziHistory_d = {nrziHistory_q[NRZI_MAXRL_ONES-2:0], sendBit};

wire doStuff = &nrziHistory_q;
wire sendBit = currentBit && !doStuff;

// }}} Calculate bit stuffing and mux into sendBit.

// {{{ Drive differential {d+, d-}.
// approx 3 dff

// SYNC_SOP and SYNC_EOP are specially defined synchronisation patterns, not
// composed of any data.
// Everything else (PID, TOKENFIELDS_*, PAYLOAD_*) is comprised of whole bytes.
// SOP is data-equivalent to 7 zeros then a single 1, so also a whole byte.
// EOP is signalled by pulling both {d+, d-} low for 2x 12MHz cycles, which has
// no data equivalent.
// TOKENFIELDS_* includes address + endpoint, or frame number, and CRC5.
//  SOP, PID, EOP
//  SOP, PID, TOKENFIELDS_0, TOKENFIELDS_1, EOP
//  SOP, PID, PAYLOAD_0, ..., PAYLOAD_n<64, CRC16_0, CRC16_1, EOP
wire finalByte_token;
generate if (AS_HOST_NOT_DEV) begin
  assign finalByte_token = pidGrp_isToken && (nBytesSent_q == 'd4);
end else begin
  assign finalByte_token = 1'b0;
end endgenerate
wire finalByte_data = pidGrp_isData && lastDataBytes_q[2];
wire finalByte_handshake = pidGrp_isHandshake && (nBytesSent_q == 'd2);
wire finalByteSent = finalByte_token || finalByte_handshake || finalByte_data;
`dff_nocg_srst(reg, eop, i_clk_12MHz, i_rst, 1'b0)
always @*
  if (bitCntr_q == 3'd3)
    eop_d = 1'b0;
  else if (finalByteSent && inflight_q)
    eop_d = 1'b1;
  else
    eop_d = eop_q;

assign o_eopDone = (bitCntr_q == 3'd3) && eop_q;

wire txSE0 = (pn_q == LINE_SE0);

`dff_cg_srst(reg [1:0], pn, i_clk_12MHz, inflight_q, i_rst, LINE_J)
always @*
  if ((bitCntr_q == 3'd2) && eop_q) // EOP must revert line back to J state.
    pn_d = LINE_J;
  else if (eop_d)
    pn_d = LINE_SE0;
  else if (!sendBit && !eop_q)
    pn_d = ~pn_q;
  else
    pn_d = pn_q;

assign {o_dp, o_dn} = pn_q;

// }}} Drive differential {d+, d-}.

// NOTE: inflight_q is equivalent in functionallity to an "output enable" in a
// bidirectional GPIO design.
// approx 1 dff
`dff_nocg_srst(reg, inflight, i_clk_12MHz, i_rst, 1'b0)
always @*
  if (drv_accepted)
    inflight_d = 1'b1;
  else if (o_eopDone)
    inflight_d = 1'b0;
  else
    inflight_d = inflight_q;

assign o_inflight = inflight_q;

assign o_ready = !inflight_q;

endmodule
