`include "dff.vh"

// The IN Protocol Engine sends data to the host.
module usbPeIn #(
  parameter N_EP_IN = 1,
  parameter MAX_IN_PACKET_SIZE = 32 // Must be in {8,16,32}
) (
  input  wire                   i_clk,
  input  wire                   i_rst,

  input  wire [6:0]             i_devAddr,

  output wire [N_EP_IN-1:0]     o_inEp_dataFree,
  input  wire [N_EP_IN-1:0]     i_inEp_dataPut,
  input  wire [7:0]             i_inEp_data,
  input  wire [N_EP_IN-1:0]     i_inEp_dataDone,
  input  wire [N_EP_IN-1:0]     i_inEp_stall,
  output wire [N_EP_IN-1:0]     o_inEp_acked,

  input  wire                   i_rxPktBegin,
  input  wire                   i_rxPktEnd,
  input  wire                   i_rxPktValid,
  input  wire [3:0]             i_rxPid,
  input  wire [6:0]             i_rxAddr,
  input  wire [3:0]             i_rxEndp,
  input  wire [10:0]            i_rxFrameNum,

  output wire                   o_txPktBegin, // Strobe to send new packet.
  input  wire                   i_txPktEnd,
  output wire [3:0]             o_txPid,
  output wire                   o_txDataAvail,
  input  wire                   i_txDataGet,
  output wire [7:0]             o_txData
);

`include "usbSpec.vh"

wire [1:0] currentEpState;
wire txDataAvail;
wire moreDataToSend;
wire ackReceived;
wire inTokenReceived;
wire setupTokenReceived;
wire tokenReceived;
wire dataBufferDoWrite;
wire inXfrBegin;
wire inXfrEnd;
wire rollbackInXfr;

reg [3:0] txPid;
reg [3:0] inEpNum;
`dff_nocg_norst(reg [7:0], txData, i_clk)
`dff_nocg_norst(reg [N_EP_IN-1:0], inEp_acked, i_clk)
`dff_nocg_srst(reg [N_EP_IN-1:0], dataToggle, i_clk, i_rst, 'd0)

// Endpoint FSM
localparam EP_READY   = 2'd0;
localparam EP_PUTTING = 2'd1;
localparam EP_GETTING = 2'd2;
localparam EP_STALL   = 2'd3;
(* mem2reg *) reg [1:0] epFsm_q [N_EP_IN]; // dff_nocg_srst
(* mem2reg *) reg [1:0] epFsm_d [N_EP_IN];

// In transfer FSM
localparam XFR_IDLE       = 2'd0;
localparam XFR_RCVD_IN    = 2'd1;
localparam XFR_SEND_DATA  = 2'd2;
localparam XFR_WAIT_ACK   = 2'd3;
`dff_nocg_srst(reg [1:0], inXfr, i_clk, i_rst, XFR_IDLE)

reg [7:0] inDataBuffer_m [MAX_IN_PACKET_SIZE * N_EP_IN];

// Address registers - one bit longer (6) than required (5) to permit
// fullness != emptyness
localparam LOG2_PKTSIZE = $clog2(MAX_IN_PACKET_SIZE);
wire [N_EP_IN-1:0] epFull; // Endpoint buffer has some space free.
(* mem2reg *) reg [LOG2_PKTSIZE:0] epPutAddr_q [N_EP_IN]; // dff_nocg_norst
(* mem2reg *) reg [LOG2_PKTSIZE:0] epPutAddr_d [N_EP_IN];
(* mem2reg *) reg [LOG2_PKTSIZE:0] epGetAddr_q [N_EP_IN]; // dff_nocg_srst
(* mem2reg *) reg [LOG2_PKTSIZE:0] epGetAddr_d [N_EP_IN];

`dff_cg_norst(reg [3:0], currentEndp, i_clk, inTokenReceived)
always @* currentEndp_d = i_rxEndp;

wire [LOG2_PKTSIZE:0] currentEpGetAddr;
wire [LOG2_PKTSIZE:0] currentEpPutAddr;
                                                /* verilator lint_off WIDTH */
assign currentEpState = epFsm_q[currentEndp_q];
assign currentEpGetAddr = epGetAddr_q[currentEndp_q];
assign currentEpPutAddr = epPutAddr_q[currentEndp_q];
                                                /* verilator lint_on  WIDTH */

// The actual address (note using only the real 5 bits of the incoming address
// + the high order buffer select)
wire [4+LOG2_PKTSIZE-1:0] bufferPutAddr;
wire [4+LOG2_PKTSIZE-1:0] bufferGetAddr;
assign bufferGetAddr = {currentEndp_q, currentEpGetAddr[LOG2_PKTSIZE-1:0]};
                                                  /* verilator lint_off WIDTH */
assign bufferPutAddr = {inEpNum, epPutAddr_q[inEpNum][LOG2_PKTSIZE-1:0]};
                                                  /* verilator lint_on  WIDTH */

assign tokenReceived =
  i_rxPktEnd &&
  i_rxPktValid &&
  i_rxPid[1:0] == 2'b01 &&
  i_rxAddr == i_devAddr &&
  i_rxEndp < N_EP_IN;

assign setupTokenReceived =
  tokenReceived &&
  i_rxPid[3:2] == 2'b11;

assign inTokenReceived =
  tokenReceived &&
  i_rxPid[3:2] == 2'b10;

assign ackReceived =
  i_rxPktEnd &&
  i_rxPktValid &&
  i_rxPid == 4'b0010;

assign moreDataToSend = currentEpGetAddr < currentEpPutAddr;

assign txDataAvail =
  inXfr_q == XFR_SEND_DATA &&
  moreDataToSend;

assign dataBufferDoWrite =
                                                /* verilator lint_off WIDTH */
  (epFsm_q[inEpNum] == EP_PUTTING) &&
  i_inEp_dataPut[inEpNum] &&
  !epPutAddr_q[inEpNum][LOG2_PKTSIZE];
                                                /* verilator lint_on  WIDTH */

assign inXfrBegin =
  (inXfr_q == XFR_RCVD_IN) &&
  (currentEpState == EP_GETTING);

assign inXfrEnd =
  (inXfr_q == XFR_WAIT_ACK) &&
  ackReceived;

// FIXME: need to handle smash/timeout
// Could wait here forever (although another token will come along)
assign rollbackInXfr =
  (inXfr_q == XFR_IDLE) ||
  ((inXfr_q == XFR_WAIT_ACK) && !ackReceived && inTokenReceived) ||
  ((inXfr_q == XFR_WAIT_ACK) && i_rxPktEnd);

//////////////////////////////////////////////////////////////////////////////

genvar e;
generate for (e=0; e < N_EP_IN; e=e+1) begin

  assign epFull[e] = epPutAddr_q[e][LOG2_PKTSIZE];

  assign o_inEp_dataFree[e] = !epFull[e] && (epFsm_q[e] == EP_PUTTING);

  always @*
    if ((inXfr_q == XFR_WAIT_ACK) && ackReceived && (currentEndp_q == e))
      dataToggle_d[e] = !dataToggle_q[e];
    else if (setupTokenReceived && (i_rxEndp == e))
      dataToggle_d[e] = 1'b1;
    else
      dataToggle_d[e] = dataToggle_q[e];

  always @* inEp_acked_d[e] =
    (epFsm_q[e] == EP_GETTING) &&
    inXfrEnd &&
    (currentEndp_q == e);

  always @*
    if ((currentEndp_q == e) && (inXfr_q == XFR_SEND_DATA) && i_txDataGet && txDataAvail)
      epGetAddr_d[e] = epGetAddr_q[e] + 'd1;
    else if ((currentEndp_q == e) && rollbackInXfr)
      epGetAddr_d[e] = '0;
    else
      epGetAddr_d[e] = epGetAddr_q[e];

  always @*
    if (epFsm_q[e] == EP_READY)
      epPutAddr_d[e] = '0;
    else if (epFsm_q[e] == EP_PUTTING && i_inEp_dataPut[e] && !epFull[e])
      epPutAddr_d[e] = epPutAddr_q[e] + 'd1;
    else
      epPutAddr_d[e] = epPutAddr_q[e];

  always @* // {{{ epFsm
    if (i_inEp_stall[e])
      epFsm_d[e] = EP_STALL;
    else
      case (epFsm_q[e])
        EP_READY:
          epFsm_d[e] = EP_PUTTING;

        EP_PUTTING:
          // If either the user says they're done or the buffer is full
          // then move on to EP_GETTING.
          if (i_inEp_dataDone[e] || epFull[e])
            epFsm_d[e] = EP_GETTING;
          else
            epFsm_d[e] = EP_PUTTING;

        EP_GETTING:
          // Waiting to send the data out, and receive an ACK token back
          // No token, and we're here for a while.
          if (inXfrEnd && currentEndp_q == e)
            epFsm_d[e] = EP_READY;
          else
            epFsm_d[e] = EP_GETTING;

        EP_STALL:
          if (setupTokenReceived && (i_rxEndp == e))
            epFsm_d[e] = EP_READY;
          else
            epFsm_d[e] = EP_STALL;

        /* Case is fully specified.
        default:
          epFsm_d[e] = EP_READY;
        */
      endcase // }}} epFsm

  always @(posedge i_clk) // dff_nocg_srst
    if (i_rst)
      epGetAddr_q[e] <= '0;
    else
      epGetAddr_q[e] <= epGetAddr_d[e];

  always @(posedge i_clk) // dff_nocg_norst
    epPutAddr_q[e] <= epPutAddr_d[e];

  always @(posedge i_clk) // dff_nocg_srst
    if (i_rst)
      epFsm_q[e] = EP_READY;
    else
      epFsm_q[e] = epFsm_d[e];

end endgenerate

// Decide which inEpNum we're talking to.
// priority encoder
integer i;
always @* begin
  inEpNum = 0;
  for (i=0; i < N_EP_IN; i=i+1)
    if (i_inEp_dataPut[i])
      inEpNum = i[3:0]; // Explicit width for lint.
end


                                                /* verilator lint_off WIDTH */
always @* txData_d = inDataBuffer_m[bufferGetAddr];
                                                /* verilator lint_on  WIDTH */

always @* // {{{ inXfr FSM
  case (inXfr_q)
    XFR_IDLE:
      if (inTokenReceived)
        inXfr_d = XFR_RCVD_IN;
      else
        inXfr_d = XFR_IDLE;

    XFR_RCVD_IN:
      if (currentEpState == EP_GETTING)
        // if we were in EP_GETTING (done getting data from the device), Send it!
        inXfr_d = XFR_SEND_DATA;
      else
        inXfr_d = XFR_IDLE;

    XFR_SEND_DATA:
      // Send the data from the buffer now (until the out (get)
      // address = the in (put) address)
      if (!moreDataToSend)
        inXfr_d = XFR_WAIT_ACK;
      else
        inXfr_d = XFR_SEND_DATA;

    XFR_WAIT_ACK:
      // FIXME: need to handle smash/timeout
      // Could wait here forever (although another token will come along)
      if (ackReceived)
        inXfr_d = XFR_IDLE;
      else if (inTokenReceived)
        inXfr_d = XFR_RCVD_IN;
      else if (i_rxPktEnd)
        inXfr_d = XFR_IDLE;
      else
        inXfr_d = XFR_WAIT_ACK;

    /* Case is fully specified.
    default:
      inXfr_d = inXfr_q;
    */
  endcase // }}} inXfr FSM

always @*
  case (inXfr_q)
    XFR_RCVD_IN: // Got an IN token
      if (currentEpState == EP_STALL)
        txPid = PID_HANDSHAKE_STALL;
      else if (currentEpState == EP_GETTING)
                                                /* verilator lint_off WIDTH */
        txPid = {dataToggle_q[currentEndp_q], 3'b011}; // DATA0/1
                                                /* verilator lint_on  WIDTH */
      else
        txPid = 4'b1010; // NAK
    default:
      txPid = 4'b0000;
  endcase

assign o_txPid = txPid;

assign o_txData = txData_q;

assign o_txDataAvail = txDataAvail;

assign o_inEp_acked = inEp_acked_q;

assign o_txPktBegin = (inXfr_q == XFR_RCVD_IN);

always @(posedge i_clk)
  if (dataBufferDoWrite)
                                                /* verilator lint_off WIDTH */
    inDataBuffer_m[bufferPutAddr] <= i_inEp_data;
                                                /* verilator lint_on  WIDTH */

endmodule
