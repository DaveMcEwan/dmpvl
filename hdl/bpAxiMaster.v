`include "dff.vh"

/* BytePipe to AXI4lite Master
  - One byte at a time in packets, header, then payload if type requires it.
  - Header, then address, then data.
  - Maximum size of BytePipe packet is 1+ADDR_BYTEW+8, for an 8B write.
  - Single outstanding request.
  - Address and data sent least significant byte first.
  - Request Header: `<request=0>[7], <rnw>[6], <prevAddr>[5], <incrAddr>[4], <nBytes-1>[3:0]`
    - Top bit always set.
    - rnw: Read-not-write
    - prevAddr: This packet does not include an address for the transaction.
      If 1 then use address of previous transaction.
    - incrAddr: Increment the stored address on reply to this transaction by the
      number of bytes in this transaction.
    - nBytes:
      Each BytePipe transaction can transfer 1,2,4, or 8 bytes.
      Onehot encoding is natural numbering (0x1, 0x2, 0x4, 0x8).
      Other values are invalid and will cause a panic packet to be sent.
  - Reply Header: `<reply=1>[7], <resp>[6:5], <panic>[4], <hint>[3:0]`
    - resp: Same encodings as AXI, 00=OKAY, 01=EXOKAY, 10=SLVERR, 11=DECERR
    - panic: If set then all state in receiver must be reset.
      resp field should be ignored when panic is set.
    - hint: May include hints such as reason for panic, or number of
      splits required to make the transaction.
      Set to 0xF for canonical panic/state-reset on immediate connection.
      Hints are not commands so receiver should be able to process reply if this
      is set to any value.
  - prevAddr is useful for push/pulling lots of data to/from the same address,
    like a hardware FIFO.
  - incrAddr, when used with prevAddr, is useful for DMA because you only need
    to send the base address.
  - On non-reset immediately send 0xFF to tell other end we're connected to
    reset any state.
  - Requested address must be naturally aligned.
*/
module bpAxiMaster #(
  parameter ADDR_BYTEW = 2, // in {1..8}. Affects both AXI interface and BytePipe protocol.
  parameter DATA_BYTEW = 4, // in {1,2,4,8}. AXI only.
  parameter AXI_MST_ID = 0, // Constant ID for master.
  parameter AXI_ID_W = 4    // AXI only.
) (
  input wire                        i_clk,
  input wire                        i_rst,

  // Signals ordered according to the document:
  // AMBA AXI and ACE Proctocol Specification
  // ARM IHI 0022D (ID102711)
  // IDs are included for interoperability with AXI4 (B1-124).

  // {{{ axi4lite master

  // Write address channel.
  output wire [AXI_ID_W-1:0]        o_axiMst_AWID,
  output wire [(8*ADDR_BYTEW)-1:0]  o_axiMst_AWADDR,
  output wire [2:0]                 o_axiMst_AWPROT,
  output wire                       o_axiMst_AWVALID,
  input  wire                       i_axiMst_AWREADY,

  // Write data channel.
  output wire [(8*DATA_BYTEW)-1:0]  o_axiMst_WDATA,
  output wire [DATA_BYTEW-1:0]      o_axiMst_WSTRB,
  output wire                       o_axiMst_WVALID,
  input  wire                       i_axiMst_WREADY,

  // Write response channel.
  input  wire [AXI_ID_W-1:0]        i_axiMst_BID, // unused. Assumed compliant.
  input  wire [1:0]                 i_axiMst_BRESP,
  input  wire                       i_axiMst_BVALID,
  output wire                       o_axiMst_BREADY,

  // Read address channel.
  output wire [AXI_ID_W-1:0]        o_axiMst_ARID,
  output wire [(8*ADDR_BYTEW)-1:0]  o_axiMst_ARADDR,
  output wire [2:0]                 o_axiMst_ARPROT,
  output wire                       o_axiMst_ARVALID,
  input  wire                       i_axiMst_ARREADY,

  // Read data channel.
  input  wire [AXI_ID_W-1:0]        i_axiMst_RID, // unused. Assumed compliant.
  input  wire [(8*DATA_BYTEW)-1:0]  i_axiMst_RDATA,
  input  wire [1:0]                 i_axiMst_RRESP,
  input  wire                       i_axiMst_RVALID,
  output wire                       o_axiMst_RREADY,

  // }}} axi4lite master

  // Incoming BytePipe
  input  wire [7:0]                 i_bp_data,
  input  wire                       i_bp_valid,
  output wire                       o_bp_ready,

  // Outgoing BytePipe
  output wire [7:0]                 o_bp_data,
  output wire                       o_bp_valid,
  input  wire                       i_bp_ready
);

genvar i;

wire bpIn_accepted = i_bp_valid && o_bp_ready;
wire bpOut_accepted = o_bp_valid && i_bp_ready;
wire axiW_accepted = o_axiMst_WVALID && i_axiMst_WREADY;
wire axiAW_accepted = o_axiMst_AWVALID && i_axiMst_AWREADY;
wire axiAR_accepted = o_axiMst_ARVALID && i_axiMst_ARREADY;
wire axiB_accepted = i_axiMst_BVALID && o_axiMst_BREADY;
wire axiR_accepted = i_axiMst_RVALID && o_axiMst_RREADY;

wire bpIn_isEop;
wire bpIn_isHdr = bpIn_accepted && (bpIn_nBytesRcvd_q == '0);

wire bpIn_isRep = bpIn_isHdr && i_bp_data[7];
wire        bpIn_rep_panic = i_bp_data[4];

wire bpIn_isReq = bpIn_isHdr && !i_bp_data[7];
wire        bpIn_req_read = i_bp_data[6];
wire        bpIn_req_write = !i_bp_data[6];
wire        bpIn_req_prevAddr = i_bp_data[5];
wire        bpIn_req_incrAddr = i_bp_data[4];
wire [3:0]  bpIn_req_nBytes = i_bp_data[3:0];

wire bpIn_isPanic = bpIn_isRep && bpIn_rep_panic;
wire doPanicRst = bpIn_isPanic || i_rst;

`dff_cg_srst(reg [4:0], bpIn_nBytesRcvd, i_clk, bpIn_accepted, doPanicRst, '0)
always @*
  if (bpIn_isEop)
    bpIn_nBytesRcvd_d = '0;
  else
    bpIn_nBytesRcvd_d = bpIn_nBytesRcvd_q + 5'd1;

// Track number of bytes remaining to receive in packet, to detect when to stop
// accepting and begin the AXI transaction.
`dff_cg_srst(reg [4:0], bpIn_nBytesPkt, i_clk, bpIn_isHdr, i_rst, '0)
always @*
  if (bpIn_isPanic)
    bpIn_nBytesPkt_d = 5'd1;                          // reply, panic
  else if (bpIn_isReq && bpIn_req_read)
    if (bpIn_req_prevAddr)
      bpIn_nBytesPkt_d = 5'd1;                        // read, no address
    else
      bpIn_nBytesPkt_d = 5'd1 + ADDR_BYTEW;           // read, with address
  else if (bpIn_isReq && bpIn_req_write)
    if (bpIn_req_prevAddr)
      bpIn_nBytesPkt_d = 5'd1 + bpIn_req_nBytes;       // write, no address
    else
      bpIn_nBytesPkt_d = 5'd1 + ADDR_BYTEW + bpIn_req_nBytes;// write, with address
  else
    bpIn_nBytesPkt_d = '1; // Unsupported case, non-panic reply maybe with data

wire singleByteReq = bpIn_isReq && bpIn_req_read && bpIn_req_prevAddr;
assign bpIn_isEop = bpIn_accepted &&
  (singleByteReq || // Single-byte request - read with no address
   bpIn_isPanic ||  // Single-byte reply - panic
   ((bpIn_nBytesRcvd_q != '0) && // Multi-byte
    (bpIn_nBytesPkt_q == (bpIn_nBytesRcvd_q+1))));

`dff_cg_srst(reg [6:0], reqHdr, i_clk, bpIn_isReq, doPanicRst, '0)
always @* reqHdr_d = i_bp_data[6:0];
wire        reqHdr_read = reqHdr_q[6];
wire        reqHdr_write = !reqHdr_q[6];
wire        reqHdr_prevAddr = reqHdr_q[5];
wire        reqHdr_incrAddr = reqHdr_q[4];
wire [3:0]  reqHdr_nBytes = reqHdr_q[3:0];

`dff_cg_norst(reg, bpIn_repNotReq, i_clk, bpIn_isHdr)
always @* bpIn_repNotReq_d = i_bp_data[7];

// Store number of bytes in the eventual response to a request.
`dff_cg_srst(reg [4:0], bpIn_nBytesResp, i_clk, bpIn_isReq, i_rst, '0)
always @*
  if (bpIn_req_read)
    bpIn_nBytesResp_d = 1 + bpIn_req_nBytes;  // header, read reply data
  else
    bpIn_nBytesResp_d = 1;                    // header only, write ack

`dff_nocg_srst(reg [4:0], bpOut_nBytesRemaining, i_clk, doPanicRst, '0)
always @*
  if (bpIn_isEop)
    if (singleByteReq)
      bpOut_nBytesRemaining_d = 5'd1 + bpIn_req_nBytes; // reply header, read data
    else if (reqHdr_read)
      bpOut_nBytesRemaining_d = 5'd1 + reqHdr_nBytes;   // reply header, read data
    else // if (reqHdr_write)
      bpOut_nBytesRemaining_d = 5'd1;                   // reply header only as write ack.
  else if (bpOut_accepted)
    bpOut_nBytesRemaining_d = bpOut_nBytesRemaining_q - 5'd1;
  else
    bpOut_nBytesRemaining_d = bpOut_nBytesRemaining_q;

wire bpOut_isEop;

`dff_nocg_srst(reg [4:0], bpOut_nBytesSent, i_clk, doPanicRst, '0)
always @*
  if (bpOut_isEop)
    bpOut_nBytesSent_d = '0;
  else if (bpOut_accepted)
    bpOut_nBytesSent_d = bpOut_nBytesSent_q + 5'd1;
  else
    bpOut_nBytesSent_d = bpOut_nBytesSent_q;

// End of reply is when we can see the last byte has been sent.
assign bpOut_isEop = bpOut_accepted &&
  (bpIn_nBytesResp_q == (bpOut_nBytesSent_q+1));


wire bpIn_reqBegin =
  bpIn_isEop &&
  (singleByteReq || !bpIn_repNotReq_q);

// Request is synthesized into one or more AXI master transactions.
// AXI4lite can only write a power-of-2 number of bytes so all transactions will
// be the same size.
// Same number applies to writes on AW, reads on AR, and read replies on R.
wire [3:0] axi_nBytesTxn;
generate if (DATA_BYTEW == 1) begin
  assign axi_nBytesTxn = 4'd1;
end else if (DATA_BYTEW == 8) begin
  assign axi_nBytesTxn = reqHdr_nBytes;
end else begin
  assign axi_nBytesTxn = (reqHdr_nBytes < DATA_BYTEW) ? reqHdr_nBytes : DATA_BYTEW;
end endgenerate

wire axiDone;

// AXI4lite can only receive whole words.
`dff_nocg_srst(reg [3:0], axiR_nBytesRcvd, i_clk, doPanicRst, '0)
always @*
  if (bpIn_reqBegin)
    axiR_nBytesRcvd_d = '0;
  else if (axiR_accepted)
    axiR_nBytesRcvd_d = axiR_nBytesRcvd_q + axi_nBytesTxn;
  else
    axiR_nBytesRcvd_d = axiR_nBytesRcvd_q;

`dff_nocg_srst(reg [3:0], axiB_nBytesAckd, i_clk, doPanicRst, '0)
always @*
  if (bpIn_reqBegin)
    axiB_nBytesAckd_d = '0;
  else if (axiB_accepted)
    axiB_nBytesAckd_d = axiB_nBytesAckd_q + axi_nBytesTxn;
  else
    axiB_nBytesAckd_d = axiB_nBytesAckd_q;

`dff_nocg_srst(reg [3:0], axiAR_nBytesReqd, i_clk, doPanicRst, '0)
always @*
  if (bpIn_reqBegin)
    axiAR_nBytesReqd_d = '0;
  else if (axiAR_accepted)
    axiAR_nBytesReqd_d = axiAR_nBytesReqd_q + axi_nBytesTxn;
  else
    axiAR_nBytesReqd_d = axiAR_nBytesReqd_q;

`dff_nocg_srst(reg [3:0], axiW_nBytesSent, i_clk, doPanicRst, '0)
always @*
  if (bpIn_reqBegin)
    axiW_nBytesSent_d = '0;
  else if (axiW_accepted)
    axiW_nBytesSent_d = axiW_nBytesSent_q + axi_nBytesTxn;
  else
    axiW_nBytesSent_d = axiW_nBytesSent_q;

`dff_nocg_srst(reg [3:0], axiAW_nBytesSent, i_clk, doPanicRst, '0)
always @*
  if (bpIn_reqBegin)
    axiAW_nBytesSent_d = '0;
  else if (axiAW_accepted)
    axiAW_nBytesSent_d = axiAW_nBytesSent_q + axi_nBytesTxn;
  else
    axiAW_nBytesSent_d = axiAW_nBytesSent_q;

// Only one type of transaction outstanding so only one counter required.
`dff_nocg_srst(reg [3:0], axiOutstandingResps, i_clk, doPanicRst, '0)
always @*
  if (axiSent && !axiRcvd)
    axiOutstandingResps_d = axiOutstandingResps_q + 1;
  else if (!axiSent && axiRcvd)
    axiOutstandingResps_d = axiOutstandingResps_q - 1;
  else
    axiOutstandingResps_d = axiOutstandingResps_q;

wire axiSent = axiAR_accepted || axiAW_accepted;
wire axiRcvd = axiR_accepted || axiB_accepted;
assign axiDone =
  axiRcvd &&
  ((reqHdr_nBytes-axi_nBytesTxn) == (reqHdr_read ? axiR_nBytesRcvd_q : axiB_nBytesAckd_q));


wire [(8*ADDR_BYTEW)-1:0] addr;
                                                  /* verilator lint_off WIDTH */
wire [(8*ADDR_BYTEW)-1:0] addrNext = addr + axi_nBytesTxn;
                                                  /* verilator lint_on  WIDTH */
(* mem2reg *) reg [7:0] addr_q [ADDR_BYTEW]; // dff_cg_norst
generate for (i=0; i < ADDR_BYTEW; i=i+1) begin : addr_b
  always @(posedge i_clk)
    if (bpIn_isPanic)
      addr_q[i] <= '0;
    else if (bpIn_nBytesRcvd_q == (i+1) && !reqHdr_prevAddr)
      addr_q[i] <= i_bp_data;
    else if (reqHdr_incrAddr && (axiAW_accepted || axiAR_accepted))
      addr_q[i] <= addrNext[8*i +: 8];

  assign addr[8*i +: 8] = addr_q[i];
end : addr_b endgenerate


wire [7:0] isThisDataByteIn;
wire [7:0] axiReplyHasThisByte;
wire [(8*8)-1:0] data;
(* mem2reg *) reg [7:0] data_q [8]; // dff_cg_norst
generate for (i=0; i < 8; i=i+1) begin : data_b
  localparam WORD_BASE_IDX = i >> $clog2(DATA_BYTEW);
  localparam WORD_OFST_IDX = i % DATA_BYTEW;

  assign isThisDataByteIn[i] =
    (reqHdr_prevAddr && (bpIn_nBytesRcvd_q == (i+1))) ||            // no address
    (!reqHdr_prevAddr && (bpIn_nBytesRcvd_q == (ADDR_BYTEW+i+1)));  // with address

  assign axiReplyHasThisByte[i] =
    axiR_accepted &&
    ((axiR_nBytesRcvd_q >> $clog2(DATA_BYTEW)) == WORD_BASE_IDX);

  always @(posedge i_clk)
    if (bpIn_isPanic)
      data_q[i] <= '0;
    else if (isThisDataByteIn[i])
      data_q[i] <= i_bp_data;
    else if (axiReplyHasThisByte[i])
      data_q[i] <= i_axiMst_RDATA[8*WORD_OFST_IDX +: 8];
    else
      data_q[i] <= data_q[i];

  assign data[8*i +: 8] = data_q[i];
end : data_b endgenerate


// BytePipe only supports nBytes to be powers of 2 so AXI write strobe will
// always be set from bottom bit.
generate if (DATA_BYTEW == 1) begin
  assign o_axiMst_WSTRB = 1'b1; // Simple for single byte AXI.
end else begin
  wire [7:0] wstrb = (1 << axi_nBytesTxn) - 1;
  assign o_axiMst_WSTRB = wstrb[DATA_BYTEW-1:0];
end endgenerate

`dff_nocg_srst(reg, wvalid, i_clk, i_rst, 1'b0)
always @*
  if (bpIn_reqBegin && reqHdr_write && !singleByteReq)
    wvalid_d = 1'b1;
  else if (axiW_accepted && (axiW_nBytesSent_d >= reqHdr_nBytes))
    wvalid_d = 1'b0;
  else
    wvalid_d = wvalid_q;

`dff_nocg_srst(reg, awvalid, i_clk, i_rst, 1'b0)
always @*
  if (bpIn_reqBegin && reqHdr_write && !singleByteReq)
    awvalid_d = 1'b1;
  else if (axiAW_accepted && (axiAW_nBytesSent_d >= reqHdr_nBytes))
    awvalid_d = 1'b0;
  else
    awvalid_d = awvalid_q;

`dff_nocg_srst(reg, arvalid, i_clk, i_rst, 1'b0)
always @*
  if ((bpIn_reqBegin && reqHdr_read) || singleByteReq)
    arvalid_d = 1'b1;
  else if (axiAR_accepted && (axiAR_nBytesReqd_d >= reqHdr_nBytes))
    arvalid_d = 1'b0;
  else
    arvalid_d = arvalid_q;

// Set o_axi_*VALID until AXI requests have been accepted.
// AXI W channel may go before AW, but not vice versa.
assign o_axiMst_WVALID = wvalid_q;
assign o_axiMst_AWVALID = awvalid_q && (axiW_nBytesSent_q >= axiAW_nBytesSent_q);
assign o_axiMst_ARVALID = arvalid_q;

assign o_axiMst_AWID = AXI_MST_ID;
assign o_axiMst_ARID = AXI_MST_ID;

assign o_axiMst_AWPROT = 3'b000;
assign o_axiMst_ARPROT = 3'b000;

assign o_axiMst_AWADDR = addr;
assign o_axiMst_ARADDR = addr;

assign o_axiMst_WDATA = data[8*axiW_nBytesSent_q +: 8*DATA_BYTEW];

`dff_nocg_srst(reg, axi_BREADY, i_clk, i_rst, 1'b0)
always @* axi_BREADY_d = reqHdr_write && (axiOutstandingResps_q != '0);

`dff_nocg_srst(reg, axi_RREADY, i_clk, i_rst, 1'b0)
always @* axi_RREADY_d = reqHdr_read && (axiOutstandingResps_q != '0);

assign o_axiMst_BREADY = axi_BREADY_q;
assign o_axiMst_RREADY = axi_RREADY_q;


// To calculate the response code just OR all AXI responses together.
// This means mixed errors combine to DECERR.
`dff_cg_srst(reg [1:0], axiResp, i_clk, (bpIn_reqBegin || axiRcvd), doPanicRst, '0)
always @*
  if (bpIn_reqBegin)
    axiResp_d = '0;
  else if (axiRcvd)
    axiResp_d = axiResp_q |
      ({2{axiR_accepted}} & i_axiMst_RRESP) |
      ({2{axiB_accepted}} & i_axiMst_BRESP);
  else
    axiResp_d = axiResp_q;


`dff_nocg_srst(reg, bpTxnOutstanding, i_clk, doPanicRst, 1'b0)
always @*
  if (bpIn_reqBegin)
    bpTxnOutstanding_d = 1'b1;
  else if (bpOut_isEop)
    bpTxnOutstanding_d = 1'b0;
  else
    bpTxnOutstanding_d = bpTxnOutstanding_q;

// Shared data flops means we cannot accept a new request until a full reply has
// been sent.
assign o_bp_ready = !bpTxnOutstanding_q;

// Wait until all has been received from AXI master reply channels before
// sending reply on BytePipe.
`dff_nocg_srst(reg, bpOut_valid, i_clk, doPanicRst, '0)
always @*
  if (axiDone)
    bpOut_valid_d = 1'b1;
  else if (bpOut_isEop)
    bpOut_valid_d = 1'b0;
  else
    bpOut_valid_d = bpOut_valid_q;

assign o_bp_valid = bpOut_valid_q;


wire [7:0] bpOut_repHdr = {1'b1, axiResp_q, 5'b00000};
wire [7:0] bpOut_repData = data[8*bpOut_nBytesSent_q +: 8];

`dff_nocg_srst(reg [7:0], bpOut_data, i_clk, doPanicRst, '0)
always @*
  if (axiDone) // header
    bpOut_data_d = bpOut_repHdr;
  else if (bpOut_accepted)
    bpOut_data_d = bpOut_repData;
  else
    bpOut_data_d = bpOut_data_q;

assign o_bp_data = bpOut_data_q;

endmodule
