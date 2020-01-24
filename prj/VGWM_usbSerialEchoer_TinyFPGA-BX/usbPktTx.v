`include "dff.vh"

module usbPktTx (
  // A 48MHz clock is required to receive USB data at 12MHz and it's simple to
  // use 48MHz everywhere.
  input  wire           i_clk_48MHz,
  input  wire           i_rst,

  // Bit strobe from rx to align with senders clock.
  input  wire           i_bitStrobe,

  output wire           o_oe,
  output wire           o_dp,
  output wire           o_dn,

  // pulse to initiate new packet transmission
  input  wire           i_pktBegin,
  output wire           o_pktEnd,

  input  wire [3:0]     i_pid,

  // tx logic pulls data until there is nothing available
  input  wire           i_txDataAvail,
  output wire           o_txDataGet,
  input  wire [7:0]     i_txData
);

`include "usbSpec.vh"

wire [1:0] pidCodingGroup;
wire pidIsToken;
wire pidIsData;
wire pidIsHandshake;
wire pidIsSpecial;

wire serialTxData;
wire bitstuff;

`dff_nocg_norst(reg [2:0], bitCount, i_clk_48MHz)
always @*
  if (i_pktBegin)
    bitCount_d = 3'd1;
  else if (i_bitStrobe && !bitstuff)
    bitCount_d = bitCount_q + 3'd1;
  else
    bitCount_d = bitCount_q;

`dff_nocg_norst(reg [NRZI_MAXRL_ONES-2:0], bitHistory, i_clk_48MHz)
always @*
  if (i_pktBegin)
    bitHistory_d = '0;
  else if (i_bitStrobe)
    bitHistory_d = {serialTxData, bitHistory_q[NRZI_MAXRL_ONES-2:1]};
  else
    bitHistory_d = bitHistory_q;

`dff_nocg_norst(reg, byteStrobe, i_clk_48MHz)
always @*
  if (i_bitStrobe && !bitstuff)
    byteStrobe_d = (bitCount_q == 3'd0);
  else
    byteStrobe_d = 1'b0;

`dff_cg_norst(reg [3:0], pid, i_clk_48MHz, i_pktBegin)
always @* pid_d = i_pid;

assign pidCodingGroup = pid_q[1:0];
assign pidIsToken     = pidCodingGroup == PIDGROUP_TOKEN;
assign pidIsData      = pidCodingGroup == PIDGROUP_DATA;
assign pidIsHandshake = pidCodingGroup == PIDGROUP_HANDSHAKE;
assign pidIsSpecial   = pidCodingGroup == PIDGROUP_SPECIAL;

assign bitstuff = &{serialTxData, bitHistory_q};

`dff_nocg_norst(reg [3:0], bitstuff, i_clk_48MHz)
always @* bitstuff_d = {bitstuff, bitstuff_q[3:1]};


// {{{ packet FSM
localparam PKT_IDLE            = 0;
localparam PKT_SYNC            = 1;
localparam PKT_PID             = 2;
localparam PKT_DATA_OR_CRC16_0 = 3;
localparam PKT_CRC16_1         = 4;
localparam PKT_EOP             = 5;

`dff_nocg_srst(reg [4:0], pktFsm, i_clk_48MHz, i_rst, PKT_IDLE)

always @*
  case (pktFsm_q)
    PKT_IDLE:
      pktFsm_d = i_pktBegin ? PKT_SYNC : pktFsm_q;

    PKT_SYNC:
      pktFsm_d = byteStrobe_q ? PKT_PID : pktFsm_q;

    PKT_PID:
      if (byteStrobe_q)
        pktFsm_d = pidIsData ? PKT_DATA_OR_CRC16_0 : PKT_EOP;
      else
        pktFsm_d = pktFsm_q;

    PKT_DATA_OR_CRC16_0:
      if (byteStrobe_q)
        pktFsm_d = i_txDataAvail ? PKT_DATA_OR_CRC16_0 : PKT_CRC16_1;
      else
        pktFsm_d = pktFsm_q;

    PKT_CRC16_1:
      pktFsm_d = byteStrobe_q ? PKT_EOP : pktFsm_q;

    PKT_EOP:
      pktFsm_d = byteStrobe_q ? PKT_IDLE : pktFsm_q;

    default:
      pktFsm_d = PKT_IDLE;
  endcase
// }}} packet FSM

`dff_nocg_norst(reg, dataPayload, i_clk_48MHz)
always @*
  if ((pktFsm_q == PKT_DATA_OR_CRC16_0) && byteStrobe_q)
    dataPayload_d = i_txDataAvail;
  else
    dataPayload_d = dataPayload_q;

`dff_nocg_norst(reg, txDataGet, i_clk_48MHz)
always @*
  if (pktFsm_q == PKT_DATA_OR_CRC16_0)
    txDataGet_d = i_txDataAvail && byteStrobe_q;
  else
    txDataGet_d = txDataGet_q;

assign o_txDataGet = txDataGet_q;



`dff_nocg_srst(reg [7:0], dataShft, i_clk_48MHz, i_rst, '0)
always @*
  if (!i_pktBegin && i_bitStrobe)
      //                      Stuff bit                 Usual deserialize
      dataShft_d = bitstuff ? {dataShft_q[7:1], 1'b0} : {1'b0, dataShft_q[7:1]};
  else if (byteStrobe_q)
    case (pktFsm_q)
      PKT_SYNC:             dataShft_d = 8'b10000000;
      PKT_PID:              dataShft_d = {~pid_q, pid_q};
      PKT_DATA_OR_CRC16_0:  dataShft_d = i_txDataAvail ? i_txData : ~crc16_q[7:0];
      PKT_CRC16_1:          dataShft_d = ~crc16_q[15:8];
      default:              dataShft_d = dataShft_q;
    endcase
  else
    dataShft_d = dataShft_q;

assign serialTxData = dataShft_q[0];


// 8.3.5.2 Data CRCs
// G(x) = x^16 + x^15 + x^2 + 1
// CRC16 calculated "backwards" since LSB is sent first.
`dff_nocg_norst(reg [15:0], crc16, i_clk_48MHz)
wire crc16Feedback;
always @*
  if (i_bitStrobe && dataPayload_q && !bitstuff_q[0] && !i_pktBegin)
    crc16_d = {crc16Feedback,
               crc16_q[15],
               crc16_q[14] ^ crc16Feedback,
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
               crc16_q[1] ^ crc16Feedback};
  else if (i_pktBegin)
    crc16_d = '1;
  else
    crc16_d = crc16_q;
assign crc16Feedback = serialTxData ^ crc16_q[0];


wire serialTxSE0;
`dff_nocg_norst(reg [7:0], se0Shft, i_clk_48MHz)

always @*
  if (!i_pktBegin && i_bitStrobe && !bitstuff)
    se0Shft_d = {1'b0, se0Shft_q[7:1]};
  else if (byteStrobe_q)
    case (pktFsm_q)
      PKT_SYNC:            se0Shft_d = '0;
      PKT_PID:             se0Shft_d = '0;
      PKT_DATA_OR_CRC16_0: se0Shft_d = '0;
      PKT_CRC16_1:         se0Shft_d = '0;
      PKT_EOP:             se0Shft_d = 8'b00000111;
      default:             se0Shft_d = se0Shft_q;
    endcase
  else
    se0Shft_d = se0Shft_q;

assign serialTxSE0 = se0Shft_q[0];

// Onehot right shift instead of counter.
`dff_nocg_norst(reg [2:0], endOfPkt, i_clk_48MHz)
always @*
  if (i_pktBegin)
    endOfPkt_d = 3'b100;
  else if (i_bitStrobe && serialTxSE0)
    endOfPkt_d = {1'b0, endOfPkt_q[2:1]};
  else
    endOfPkt_d = endOfPkt_q;

// Take control of {d+, d-} IO pins.
`dff_nocg_srst(reg [7:0], oeShft, i_clk_48MHz, i_rst, '0)
`dff_cg_srst(reg, outputEnable, i_clk_48MHz, (!i_pktBegin && i_bitStrobe), i_rst, 1'b0)

always @*
  if (!i_pktBegin && i_bitStrobe && !bitstuff)
    oeShft_d = {1'b0, oeShft_q[7:1]};
  else if (byteStrobe_q)
    case (pktFsm_q)
      PKT_SYNC:            oeShft_d = '1;
      PKT_PID:             oeShft_d = '1;
      PKT_DATA_OR_CRC16_0: oeShft_d = '1;
      PKT_CRC16_1:         oeShft_d = '1;
      PKT_EOP:             oeShft_d = 8'b00000111;
      default:             oeShft_d = oeShft_q;
    endcase
  else
    oeShft_d = oeShft_q;

always @* outputEnable_d = oeShft_q[0];

assign o_oe = outputEnable_q;

// Drive differential {d+, d-}.
`dff_nocg_srst(reg [1:0], pn, i_clk_48MHz, i_rst || i_pktBegin, LINE_J)
always @*
  if (i_bitStrobe && serialTxSE0)
    pn_d = {endOfPkt_q[0], 1'b0};
  else if (i_bitStrobe && !serialTxData)
    pn_d = ~pn_q;
  else
    pn_d = pn_q;

assign o_dp = pn_q[1];
assign o_dn = pn_q[0];

assign o_pktEnd = i_bitStrobe && (se0Shft_q[1:0] == 2'b01);

endmodule
