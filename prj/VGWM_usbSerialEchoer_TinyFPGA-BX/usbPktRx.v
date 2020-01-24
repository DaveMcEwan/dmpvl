`include "dff.vh"

module usbPktRx (
  // A 48MHz clock is required to recover the clock from the incoming data.
  input  wire           i_clk_48MHz,
  input  wire           i_rst,

  // USB data+ and data- lines.
  input  wire           i_dp,
  input  wire           i_dn,

  // Pulse on every bit transition to synchronise with usbPktTx.
  output wire           o_bitStrobe,

  // Pulse on beginning and end of each packet.
  output wire           o_pktBegin,
  output wire           o_pktEnd,

  // Most recent packet decoded.
  output wire [3:0]     o_pid,  // Packed identifier
  output wire [6:0]     o_addr,
  output wire [3:0]     o_endp,
  output wire [10:0]    o_frameNum, // Only with Start-Of-Frame token packets.

  output wire           o_dataPut, // Pulse on valid data on o_data.
  output wire [7:0]     o_data,

  // Most recent packet passes PID and CRC checks
  output wire           o_pktValid
);

`include "usbSpec.vh"

/*
dp_q[1]        _------------____________________________------------------
dn_q[1]        -____________----------------------------__________________
diffTrans_q    _----____________----________________________----__________
lineState_q     ?   J   J   J   ?   K   K   K   K   K   K   ?   J   J   J
bitPhase_q      0   0   1   2   3   0   1   2   3   0   1   2   0   1   2
lineStateValid _________----____________----____________----________----__
*/
localparam TRANS_INIT = {LINE_J, LINE_J, LINE_J};
localparam TRANS_SOP = {LINE_J, LINE_K, LINE_K};
localparam TRANS_EOP = {LINE_SE0, LINE_SE0};

// Double flop raw inputs for metastability mitigation.
`dff_nocg_norst(reg [1:0], dp, i_clk_48MHz)
`dff_nocg_norst(reg [1:0], dn, i_clk_48MHz)
always @* dp_d = {dp_q[0], i_dp};
always @* dn_d = {dn_q[0], i_dn};

wire [1:0] diffPair;
assign diffPair = {dp_q[1], dn_q[1]};


wire lineStateValid;
`dff_nocg_norst(reg, diffTrans, i_clk_48MHz)
`dff_cg_srst(reg [1:0], lineState, i_clk_48MHz, diffTrans_q, i_rst, '0)
`dff_cg_srst(reg [5:0], lineHistory, i_clk_48MHz, lineStateValid, i_rst, TRANS_INIT)

always @* diffTrans_d = (diffPair != lineState_q);
always @* lineState_d = diffPair;
always @* lineHistory_d = {lineHistory_q[3:0], lineState_q};

// 8.2 SYNC Field, p145
wire pktBegin;
wire pktEnd;

`dff_cg_srst(reg, pktInFlight, i_clk_48MHz, lineStateValid, i_rst, 1'b0)
always @*
  if (pktBegin)
    pktInFlight_d = 1'b1;
  else if (pktEnd)
    pktInFlight_d = 1'b0;
  else
    pktInFlight_d = pktInFlight_q;

assign pktBegin = !pktInFlight_q && (lineHistory_q == TRANS_SOP);
assign pktEnd = pktInFlight_q && (lineHistory_q[3:0] == TRANS_EOP);

assign o_pktBegin = pktBegin;
assign o_pktEnd = pktEnd;


`dff_nocg_norst(reg [1:0], bitPhase, i_clk_48MHz)
// In simulation this requires a known value in order to keep the 12MHz strobe
// running from the 48MHz clock, but in implementation we don't care what the
// value is since it will just wrap and keep the strobe running anyway.
wire [1:0] synth_bitPhase_d = diffTrans_q ? '0 : bitPhase_q + 2'd1;
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
  else if ($isunknown(diffTrans_q))
    bitPhase_d = bitPhase_q + 2'd1;
  else
    bitPhase_d = synth_bitPhase_d;
  `endif
`endif

// Line state is sampled in the middle of the bit time.
assign lineStateValid = (bitPhase_q == 2'd1);

// diffTrans_q is used to align to transmit clock.
assign o_bitStrobe = (bitPhase_q == 2'd2);


// NRZI decode
wire dinValidRaw;
wire din;

assign dinValidRaw =
 pktInFlight_q &&
 lineStateValid &&
 ((lineHistory_q[3:0] == NRZI_ENC0_A) ||
  (lineHistory_q[3:0] == NRZI_ENC0_B) ||
  (lineHistory_q[3:0] == NRZI_ENC1_A) ||
  (lineHistory_q[3:0] == NRZI_ENC1_B));

assign din =
 (lineHistory_q[3:0] == NRZI_ENC1_A) ||
 (lineHistory_q[3:0] == NRZI_ENC1_B);

// 7.1.6 Bit Stuffing check.
wire dinValid;
wire dinRL1Invalid;
`dff_nocg_srst(reg [NRZI_MAXRL_ONES-1:0], dinShft, i_clk_48MHz, i_rst, 'd0)
always @*
  if (pktEnd)
    dinShft_d = 'd0;
  else if (dinValidRaw)
    dinShft_d = {dinShft_q[NRZI_MAXRL_ONES-2:0], din};
  else
    dinShft_d = dinShft_q;

assign dinRL1Invalid = &dinShft_q; // Too many consecutive 1's.
assign dinValid = dinValidRaw && !dinRL1Invalid;

// 8.3.1 Packet Identifier (PID) Field, p145
wire pidComplete;
`dff_nocg_norst(reg [8:0], pid, i_clk_48MHz)
wire pidValid;
wire [1:0] pidCodingGroup;
wire pidIsToken;
wire pidIsData;
wire pidIsHandshake;
wire pidIsSpecial;
wire [3:0] pidValue;

// Shift in 8b PID field LSB first, with 9th bit as a sentinal.
always @*
  if (dinValid && !pidComplete)
    pid_d = {din, pid_q[8:1]};
  else if (pktBegin)
    pid_d = 9'b100000000; // Sentinal bit which gets shifted down.
  else
    pid_d = pid_q;

assign pidComplete = pid_q[0];
assign pidValid = ((~pid_q[8:5]) == pid_q[4:1]);
assign pidCodingGroup = pid_q[2:1];
assign pidIsToken     = pidCodingGroup == PIDGROUP_TOKEN;
assign pidIsData      = pidCodingGroup == PIDGROUP_DATA;
assign pidIsHandshake = pidCodingGroup == PIDGROUP_HANDSHAKE;
assign pidIsSpecial   = pidCodingGroup == PIDGROUP_SPECIAL;
assign pidValue = pid_q[4:1];

assign o_pid = pidValue;


// 8.3.5.1 Token CRCs
// G(x) = x^5 + x^2 + 1
`dff_nocg_norst(reg [4:0], crc5, i_clk_48MHz)
wire crc5Feedback;
wire crc5Valid;
always @*
  if (dinValid && pidComplete)
    crc5_d = {crc5_q[3],
              crc5_q[2],
              crc5_q[1] ^ crc5Feedback,
              crc5_q[0],
              crc5Feedback};
  else if (pktBegin)
    crc5_d = '1;
  else
    crc5_d = crc5_q;
assign crc5Feedback = crc5_q[4] ^ din;
assign crc5Valid = (crc5_q == TOKEN_CRC_RESIDUAL);


// 8.3.5.2 Data CRCs
// G(x) = x^16 + x^15 + x^2 + 1
`dff_nocg_norst(reg [15:0], crc16, i_clk_48MHz)
wire crc16Feedback;
wire crc16Valid;
always @*
  if (dinValid && pidComplete)
    crc16_d = {crc16_q[14] ^ crc16Feedback,
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
               crc16_q[1] ^ crc16Feedback,
               crc16_q[0],
               crc16Feedback};
  else if (pktBegin)
    crc16_d = '1;
  else
    crc16_d = crc16_q;
assign crc16Feedback = crc16_q[15] ^ din;
assign crc16Valid = (crc16_q == DATA_CRC_RESIDUAL);

// 8.4.1 Token Packets          {PID:8b, ADDR:7b, ENDP:4b, CRC5:5b}
// 8.4.2 Start of Frame Packets {PID:8b, Frame Number:11b, CRC5:5b}
// 8.4.2 Data Packets           {PID:8b, data:0..1023b, CRC16:16b}
// 8.4.4 Handshake Packets      {PID:8b}

// Shift in 7b ADDR field then 4b ENDP field LSB first.
// Use same flops for 11b SOF packet frame number field.
wire tokenComplete;
wire tokenInFlight;
`dff_cg_norst(reg [SOF_FIELD_FRAMENUMBER_LENGTH-1:0], token, i_clk_48MHz, tokenInFlight)
`dff_nocg_srst(reg [3:0], tokenBitcntr, i_clk_48MHz, i_rst, 4'd0)
wire [6:0] tokenFieldAddr;
wire [3:0] tokenFieldEndp;
wire [10:0] sofFieldFrameNumber;

always @*
  if (tokenInFlight)
    tokenBitcntr_d = tokenBitcntr_q + 4'd1;
  else if (pktBegin)
    tokenBitcntr_d = 4'd0;
  else
    tokenBitcntr_d = tokenBitcntr_q;

assign tokenComplete = (tokenBitcntr_q == SOF_FIELD_FRAMENUMBER_LENGTH);

assign tokenInFlight =
  dinValid &&
  !tokenComplete &&
  pidComplete &&
  pidIsToken;

always @* token_d = {din, token_q[SOF_FIELD_FRAMENUMBER_LENGTH-1:1]};

assign tokenFieldAddr = token_q[6:0];
assign tokenFieldEndp = token_q[10:7];
assign sofFieldFrameNumber = token_q;

assign o_addr = tokenFieldAddr;
assign o_endp = tokenFieldEndp;
assign o_frameNum = sofFieldFrameNumber;


// Shift each byte of data in LSB first, and set o_dataPut to store the byte
// in usbPeOut/outEpDataBuffer_m.
wire databytesInFlight;
wire databytePut;
`dff_cg_norst(reg [7:0], databyte, i_clk_48MHz, databytesInFlight)
`dff_nocg_srst(reg [3:0], databyteBitcntr, i_clk_48MHz, i_rst, 4'd0)

always @*
  if (databytesInFlight)
    databyteBitcntr_d = databyteBitcntr_q + 4'd1;
  else if (databytePut)
    databyteBitcntr_d = 4'd0;
  else
    databyteBitcntr_d = databyteBitcntr_q;

assign databytePut = databyteBitcntr_q[3]; // databyteBitcntr_q == 4'd8

assign databytesInFlight =
  dinValid &&
  pidComplete &&
  pidIsData;

always @* databyte_d = {din, databyte_q[7:1]};

assign o_dataPut = databytePut;
assign o_data = databyte_q;


`dff_nocg_srst(reg, pktValid, i_clk_48MHz, i_rst, 1'b0)
always @* pktValid_d =
  pidValid &&
  ((pidIsToken && crc5Valid) ||
   (pidIsData && crc16Valid) ||
   pidIsHandshake);

assign o_pktValid = pktValid_q;

endmodule // usb_fs_rx
