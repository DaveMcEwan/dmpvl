`include "asrt.vh"
`include "dff.vh"

module usbfsPktRx #(
  parameter AS_HOST_NOT_DEV = 0, // 1=Operate as host, 0=Operate as device/function.
  parameter MAX_PKT = 8  // in {8,16,32,64}. wMaxPacketSize
) (
  input  wire                       i_clk_48MHz,
  input  wire                       i_rst,

  // Output recovered 12MHz clock.
  // NOTE: This isn't quite a clock, the duty cycle will be approx 0.25.
  output wire                       o_strobe_12MHz,

  // USB {d+, d-}.
  input  wire                       i_dp,
  input  wire                       i_dn,

  // Pulse for a single 48MHz cycle when SOP/EOP is detected.
  output wire                       o_sop,
  output wire                       o_eop,

  // Remain high from SOP until EOP.
  output wire                       o_inflight,

  // PID from the last packet received.
  // ADDR,ENDP fields from the last OUT/SETUP token received.
  // Data fields from the last data payload received.
  // Setup before the o_eop pulse.
  output wire [3:0]                 o_pid,
  output wire [8*MAX_PKT-1:0]       o_lastData,
  output wire [$clog2(MAX_PKT):0]   o_lastData_nBytes,
  output wire [6:0]                 o_lastAddr,
  output wire [3:0]                 o_lastEndp,

  // Results of the integrity checks from the last packet received.
  // Must be used in conjunction with o_pid to determine corruption.
  // Setup before the o_eop pulse.
  output wire                       o_pidOkay,    // PID check passed.
  output wire                       o_tokenOkay,  // CRC5 passed
  output wire                       o_dataOkay    // CRC16 passed
);
// NOTE: A design/implementation based on this logic uses approximately TODO?? DFFs,
// assuming that the data sink is external.

`include "usbSpec.vh"

// {{{ Transition detection and clock recovery
// approx 9 dff

// Double flop raw inputs for metastability mitigation.
`dff_nocg_norst(reg [3:0], pnStabilize, i_clk_48MHz)
always @* pnStabilize_d = {pnStabilize_q[1:0], i_dp, i_dn};

`dff_nocg_norst(reg, transition, i_clk_48MHz)
`dff_cg_srst(reg [1:0], pn, i_clk_48MHz, transition_q, i_rst, LINE_J)
always @* pn_d = pnStabilize_q[3:2];
always @* transition_d = (pn_d != pn_q);

// In simulation this requires a known value in order to keep the 12MHz strobe
// running from the 48MHz clock, but in implementation we don't care what the
// value is since it will just wrap and keep the strobe running anyway.
`dff_nocg_norst(reg [1:0], bitPhase, i_clk_48MHz)
wire [1:0] synth_bitPhase_d = transition_q ? '0 : bitPhase_q + 2'd1;
`ifdef SYNTHESIS
always @* bitPhase_d = synth_bitPhase_d;
`else
  `ifdef VERILATOR
always @* bitPhase_d = synth_bitPhase_d;
  `else
initial bitPhase_q = $urandom_range(3, 0);
always @*
  if ($isunknown(bitPhase_q))
    bitPhase_d = $urandom_range(3, 0);
  else if ($isunknown(transition_q))
    bitPhase_d = bitPhase_q + 2'd1;
  else
    bitPhase_d = synth_bitPhase_d;
  `endif
`endif

assign o_strobe_12MHz = (bitPhase_q == 2'd2);

// Sample line in fixed point of bit period.
wire sampleStrobe_12MHz = (bitPhase_q == 2'd1);

// }}} Transition detection and clock recovery

// {{{ Detect SOP and EOP sequences.
// approx 7 dff

// Store the last 3 states to detect SYNC/ENC0/ENC1 sequences.
localparam TRANS_INIT = {LINE_J, LINE_J, LINE_J};
`dff_cg_srst(reg [5:0], pnSequence, i_clk_48MHz, sampleStrobe_12MHz, i_rst, TRANS_INIT)
always @* pnSequence_d = {pnSequence_q[3:0], pn_q};

// NOTE: Babble detection/protection could be performed here by clearing
// inflight_q when the frame cycle counter wraps at 48k, but it should be done
// by the nearest hub.
localparam TRANS_SOP = {LINE_J, LINE_K, LINE_K};
localparam TRANS_EOP = {LINE_SE0, LINE_SE0};
wire sop = !inflight_q && (pnSequence_q == TRANS_SOP);
wire eop = inflight_q && (pnSequence_q[3:0] == TRANS_EOP);
`dff_cg_srst(reg, inflight, i_clk_48MHz, sampleStrobe_12MHz, i_rst, 1'b0)
always @*
  if (o_sop)
    inflight_d = 1'b1;
  else if (eop_d)
    inflight_d = 1'b0;
  else
    inflight_d = inflight_q;

assign o_sop = sop && sampleStrobe_12MHz;
assign o_inflight = inflight_q;

// NOTE: o_eop may drive a lot of logic in transactor so consider flopping.
// Delaying o_eop by one cycle also has the effect of postponing o_oe in
// reaction to a packet, avoiding both host and device asserting o_oe and
// driving against each other.
`dff_nocg_srst(reg, eop, i_clk_48MHz, i_rst, 1'b0)
always @* eop_d = eop && sampleStrobe_12MHz;
assign o_eop = eop_q;

wire rxSE0 = (pn_q == LINE_SE0);

// }}} Detect SOP and EOP sequences.

// {{{ NRZI bit unstuffing.
// approx 6 dff

wire din = !(pnSequence_q[2] ^ pnSequence_q[0]);
wire jkTrans = (^pnSequence_q[3:2]) && (^pnSequence_q[1:0]);

`dff_cg_srst(reg [NRZI_MAXRL_ONES-1:0], nrziHistory, i_clk_48MHz, sampleStrobe_12MHz, i_rst, '0)
always @*
  if (sop)
    nrziHistory_d = 'd0;
  else if (jkTrans && inflight_q)
    nrziHistory_d = {nrziHistory_q[NRZI_MAXRL_ONES-2:0], din};
  else
    nrziHistory_d = nrziHistory_q;

wire discardStuffedBit = &nrziHistory_q;

wire sampleDin =
  jkTrans &&
  inflight_q &&
  !discardStuffedBit &&
  sampleStrobe_12MHz;

// }}} NRZI bit unstuffing.

// {{{ Count bits and bytes.

`dff_cg_srst(reg [2:0], bitCntr, i_clk_48MHz, sampleDin, sop, '0)
always @* bitCntr_d = bitCntr_q + 3'd1;

wire byteRcvd = (bitCntr_q == '1) && sampleDin;

//// Delay sampleDin by one 48MHz cycle to use for sampling byteShift_q.
//`dff_nocg_norst_d(reg, byteRcvd, i_clk_48MHz, byteRcvd)

// Max number of bytes in a packet is (1<SOP> + 1<PID> + MAX_PKT + 2<CRC16>)
// PID is always sent when (nBytesSent_q == 0).
// Token fields byte0 is always sent when (nBytesSent_q == 1).
// Token fields byte1 (with crc5) is always sent when (nBytesSent_q == 2).
`dff_cg_srst(reg [$clog2(MAX_PKT):0], nBytesRcvd, i_clk_48MHz, byteRcvd, sop, '0)
always @* nBytesRcvd_d = nBytesRcvd_q + 1;

// All packets and fields are an integer number of bytes in length.
// LSB always sent first --> right shift.
`dff_cg_norst(reg [7:0], byteShift, i_clk_48MHz, sampleDin)
always @* byteShift_d = {din, byteShift_q[7:1]};

// }}} Count bits and bytes.

// {{{ Decode and check PID.

wire samplePid = byteRcvd && (nBytesRcvd_q == 'd0);

`dff_cg_norst(reg [3:0], pid, i_clk_48MHz, samplePid)
always @* pid_d = byteShift_d[3:0];
assign o_pid = pid_q;

`dff_cg_srst(reg, pidOkay, i_clk_48MHz, samplePid, sop, 1'b0)
always @* pidOkay_d = (~byteShift_d[7:4] == byteShift_d[3:0]);
assign o_pidOkay = pidOkay_q;

// }}} Decode and check PID.

// {{{ PID sanity check

wire [1:0] pidCodingGroup = pid_q[1:0];
wire pidGrp_isToken     = (pidCodingGroup == PIDGROUP_TOKEN);
wire pidGrp_isData      = (pidCodingGroup == PIDGROUP_DATA);
wire pidGrp_isHandshake = (pidCodingGroup == PIDGROUP_HANDSHAKE);
wire pidGrp_isSpecial   = (pidCodingGroup == PIDGROUP_SPECIAL);

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
  assign pid_type_onehot = $onehot(devToHostPids);
end else begin
  assign pid_type_onehot = $onehot(hostToDevPids);
end endgenerate

// Assume requests have sane values for i_pid.
`asrt(pid_type_onehot, i_clk_48MHz, !i_rst && eop, pid_type_onehot)
`endif

// }}} PID sanity check

// {{{ Calculate CRCs.
// approx 21 dff

// 8.3.5.1 Token CRC
// G(x) = x^5 + x^2 + 1
`dff_cg_srst(reg [4:0], crc5, i_clk_48MHz, sampleDin, sop, '1)
wire crc5Loop = crc5_q[4] ^ din;
always @*
  if (nBytesRcvd_q != '0)
    crc5_d = {crc5_q[3],
              crc5_q[2],
              crc5_q[1] ^ crc5Loop,
              crc5_q[0],
              crc5Loop};
  else
    crc5_d = crc5_q;

assign o_tokenOkay = (crc5_q == TOKEN_CRC_RESIDUAL);

// 8.3.5.2 Data CRC
// G(x) = x^16 + x^15 + x^2 + 1
`dff_cg_srst(reg [15:0], crc16, i_clk_48MHz, sampleDin, sop, '1)
wire crc16Loop = crc16_q[15] ^ din;
always @*
  if (nBytesRcvd_q != '0)
    crc16_d = {crc16_q[14] ^ crc16Loop,
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
               crc16_q[1] ^ crc16Loop,
               crc16_q[0],
               crc16Loop};
  else
    crc16_d = crc16_q;

assign o_dataOkay = (crc16_q == DATA_CRC_RESIDUAL);

// }}} Calculate CRCs.

// {{{ Decode ADDR,ENDP.
// approx 11 dff

wire sampleTokenField0 = byteRcvd && (nBytesRcvd_q == 'd1) && pidGrp_isToken;
wire sampleTokenField1 = byteRcvd && (nBytesRcvd_q == 'd2) && pidGrp_isToken;

`dff_cg_norst_d(reg [7:0], tokenField0, i_clk_48MHz, sampleTokenField0, byteShift_d)
`dff_cg_norst_d(reg [2:0], tokenField1, i_clk_48MHz, sampleTokenField1, byteShift_d[2:0])

assign o_lastAddr = tokenField0_q[6:0];
assign o_lastEndp = {tokenField1_q, tokenField0_q[7]};

// }}} Decode ADDR,ENDP.

// {{{ Decode data and data_nBytes.
// Design/implementation should use different logic here.

wire clearDataCntr = samplePid && (byteShift_d[1:0] == PIDGROUP_DATA);
wire incrDataCntr = byteRcvd && pidGrp_isData;
`dff_cg_srst(reg [$clog2(MAX_PKT):0], data_nBytes, i_clk_48MHz, byteRcvd, clearDataCntr, '0)
always @* data_nBytes_d = incrDataCntr ? data_nBytes_q + 1 : data_nBytes_q;

assign o_lastData_nBytes = (data_nBytes_q - 'd2);

// NOTE: Due to the way the verif components pass data around and take the
// entire value at once, this must be converted to registers.
(* mem2reg *) reg [7:0] data_m [MAX_PKT];
wire [MAX_PKT-1:0] writeByte;
genvar b;
generate for (b=0; b < MAX_PKT; b=b+1) begin
  assign writeByte[b] = byteRcvd && (data_nBytes_q == b) && pidGrp_isData;

  always @(posedge i_clk_48MHz)
    if (writeByte[b]) data_m[b] <= byteShift_d;

  assign o_lastData[8*b +: 8] = data_m[b]; // NOTE: Prevents synth to mem.
end endgenerate

// }}} Decode data and data_nBytes.

// {{{ Display received packet
`ifndef SYNTHESIS

wire [10:0] tokenFrameNumber = {o_lastEndp, o_lastAddr};

always @(posedge i_clk_48MHz) if (o_eop) begin : info
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
    $sformat(s_data, " data=0x%0h, nBytes=%0d", o_lastData, o_lastData_nBytes);
  else if (pid_isTokenSof)
    $sformat(s_data, " frameNumber=%0d", tokenFrameNumber);
  else if (pidGrp_isToken)
    $sformat(s_data, " addr=%0d, endp=%0d", o_lastAddr, o_lastEndp);
  else if (pidGrp_isHandshake)
    $sformat(s_data, "");
  else
    $sformat(s_data, " UNKNOWN PIDGRP");

  $display("INFO:t%0t:%m: Received %s%s.", $time, s_pid, s_data);
end : info

`endif
// }}} Display received packet

endmodule
