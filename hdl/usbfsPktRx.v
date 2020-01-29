`include "asrt.vh"
`include "dff.vh"

module usbfsPktRx #(
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
  output wire [6:0]                 o_addr,
  output wire [3:0]                 o_endp,

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

// Max number of bytes in a packet is (1<SOP> + 1<PID> + MAX_PKT + 2<CRC16>)
// SOP is always sent when (nBytesSent_q == 0).
// PID is always sent when (nBytesSent_q == 1).
localparam NBYTES_W = $clog2(MAX_PKT) + 1;

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
  if (sop)
    inflight_d = 1'b1;
  else if (eop_d)
    inflight_d = 1'b0;
  else
    inflight_d = inflight_q;

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
wire possibleSampleDin = jkTrans && inflight_q && sampleStrobe_12MHz;

`dff_cg_srst(reg [NRZI_MAXRL_ONES-1:0], nrziHistory, i_clk_48MHz, possibleSampleDin, sop || i_rst, '0)
always @* nrziHistory_d = {nrziHistory_q[NRZI_MAXRL_ONES-2:0], din};

wire discardStuffedBit = &nrziHistory_q;

wire sampleDin = possibleSampleDin && !discardStuffedBit;

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
`dff_cg_srst(reg [NBYTES_W-1:0], nBytesRcvd, i_clk_48MHz, byteRcvd, sop, '0)
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

wire [1:0] pidCodingGroup = pid_q[1:0];
wire pidGrp_isToken = (pidCodingGroup == PIDGROUP_TOKEN);
wire pidGrp_isData  = (pidCodingGroup == PIDGROUP_DATA);

// }}} Decode and check PID.

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

assign o_addr = tokenField0_q[6:0];
assign o_endp = {tokenField1_q, tokenField0_q[7]};

// }}} Decode ADDR,ENDP.

// {{{ Decode data and data_nBytes.
// Design/implementation should use different logic here.

wire clearDataCntr = samplePid && (byteShift_d[1:0] == PIDGROUP_DATA);
wire incrDataCntr = byteRcvd && pidGrp_isData;
`dff_cg_srst(reg [NBYTES_W-1:0], data_nBytes, i_clk_48MHz, byteRcvd, clearDataCntr, '0)
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

wire pid_isTokenIn    = (pid_q == PID_TOKEN_IN);
wire pid_isTokenOut   = (pid_q == PID_TOKEN_OUT);
wire pid_isTokenSetup = (pid_q == PID_TOKEN_SETUP);
wire pid_isTokenSof   = (pid_q == PID_TOKEN_SOF);
wire pid_isData0 = (pid_q == PID_DATA_DATA0);
wire pid_isData1 = (pid_q == PID_DATA_DATA1);
wire pid_isHandshakeAck   = (pid_q == PID_HANDSHAKE_ACK);

wire [6:0] hostToDevPids = {
  pid_isTokenIn,
  pid_isTokenOut,
  pid_isTokenSetup,
  pid_isTokenSof,
  pid_isData0,
  pid_isData1,
  pid_isHandshakeAck};

wire pid_type_onehot = $onehot(hostToDevPids);

// Assume requests have sane values for i_pid.
`asrt(pid_type_onehot, i_clk_48MHz, !i_rst && eop, pid_type_onehot)

wire [10:0] tokenFrameNumber = {o_endp, o_addr};
wire pidGrp_isHandshake = (pidCodingGroup == PIDGROUP_HANDSHAKE);

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
  else
    $sformat(s_pidName, "UNKNOWN");

  $sformat(s_pid, "pid=%h=%s", pid_q, s_pidName);

  if (pidGrp_isData)
    $sformat(s_data, " data=0x%0h, nBytes=%0d", o_lastData, o_lastData_nBytes);
  else if (pid_isTokenSof)
    $sformat(s_data, " frameNumber=%0d", tokenFrameNumber);
  else if (pidGrp_isToken)
    $sformat(s_data, " addr=%0d, endp=%0d", o_addr, o_endp);
  else if (pidGrp_isHandshake)
    $sformat(s_data, "");
  else
    $sformat(s_data, " UNKNOWN PIDGRP");

  $display("INFO:t%0t:%m: Received %s%s.", $time, s_pid, s_data);
end : info

`endif
// }}} Display received packet

endmodule
