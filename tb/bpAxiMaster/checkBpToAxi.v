`include "dff.vh"
`include "asrt.vh"

// Checkers for bpAxiMaster_tb.
module checkBpToAxi #(
  parameter DATA_BYTEW = 4, // in {1,2,4,8} affects AXI widths.
  parameter ADDR_BYTEW = 2, // in {1..8}. Affects BytePipe protocol and AXI widths.
  parameter AXI_ID_W = 1    // AXI only.
)  (
  input  wire                       i_clk,
  input  wire                       i_rst,

  input  wire [AXI_ID_W-1:0]        i_axi_AWID,
  input  wire [8*ADDR_BYTEW-1:0]    i_axi_AWADDR,
  input  wire [2:0]                 i_axi_AWPROT,
  input  wire                       i_axi_AWVALID,
  input  wire                       i_axi_AWREADY,

  // Write data channel.
  input  wire [(DATA_BYTEW*8)-1:0]  i_axi_WDATA,
  input  wire [DATA_BYTEW-1:0]      i_axi_WSTRB,
  input  wire                       i_axi_WVALID,
  input  wire                       i_axi_WREADY,

  // Write response channel.
  input  wire [AXI_ID_W-1:0]        i_axi_BID,
  input  wire [1:0]                 i_axi_BRESP,
  input  wire                       i_axi_BVALID,
  input  wire                       i_axi_BREADY,

  // Read address channel.
  input  wire [AXI_ID_W-1:0]        i_axi_ARID,
  input  wire [8*ADDR_BYTEW-1:0]    i_axi_ARADDR,
  input  wire [2:0]                 i_axi_ARPROT,
  input  wire                       i_axi_ARVALID,
  input  wire                       i_axi_ARREADY,

  // Read data channel.
  input  wire [AXI_ID_W-1:0]        i_axi_RID,
  input  wire [(DATA_BYTEW*8)-1:0]  i_axi_RDATA,
  input  wire [1:0]                 i_axi_RRESP,
  input  wire                       i_axi_RVALID,
  input  wire                       i_axi_RREADY,

  // Request
  input  wire                       i_bpIn_ready,
  input  wire                       i_bpIn_valid,
  input  wire [7:0]                 i_bpIn_data,

  // Reply
  input  wire                       i_bpOut_ready,
  input  wire                       i_bpOut_valid,
  input  wire [7:0]                 i_bpOut_data
);

// TODO: More checkers

// {{{ support logic

wire bpIn_accepted = i_bpIn_ready && i_bpIn_valid;
wire bpOut_accepted = i_bpOut_ready && i_bpOut_valid;

wire axiAW_accepted = i_axi_AWREADY && i_axi_AWVALID;
wire axiW_accepted = i_axi_WREADY && i_axi_WVALID;
wire axiB_accepted = i_axi_BREADY && i_axi_BVALID;
wire axiAR_accepted = i_axi_ARREADY && i_axi_ARVALID;
wire axiR_accepted = i_axi_RREADY && i_axi_RVALID;
wire axiAny_accepted = |{axiAW_accepted,
                         axiW_accepted,
                         axiB_accepted,
                         axiAR_accepted,
                         axiR_accepted};

wire bpIn_isHdr;
wire bpIn_isRep = bpIn_isHdr && i_bpIn_data[7];
wire [1:0]  bpIn_rep_resp = i_bpIn_data[6:5];
wire        bpIn_rep_panic = i_bpIn_data[4];
wire [3:0]  bpIn_rep_hint = i_bpIn_data[3:0];

wire bpIn_isReq = bpIn_isHdr && !i_bpIn_data[7];
wire        bpIn_req_read = i_bpIn_data[6];
wire        bpIn_req_write = !i_bpIn_data[6];
wire        bpIn_req_prevAddr = i_bpIn_data[5];
wire        bpIn_req_incrAddr = i_bpIn_data[4];
wire [3:0]  bpIn_req_nBytes = i_bpIn_data[3:0];

wire bpOut_isHdr;
wire bpOut_isRep = bpOut_isHdr && i_bpOut_data[7];
wire [1:0]  bpOut_rep_resp = i_bpOut_data[6:5];
wire        bpOut_rep_panic = i_bpOut_data[4];
wire [3:0]  bpOut_rep_hint = i_bpOut_data[3:0];

wire bpOut_isReq = bpOut_isHdr && !i_bpOut_data[7];
wire        bpOut_req_read = i_bpOut_data[6];
wire        bpOut_req_write = !i_bpOut_data[6];
wire        bpOut_req_prevAddr = i_bpOut_data[5];
wire        bpOut_req_incrAddr = i_bpOut_data[4];
wire [3:0]  bpOut_req_nBytes = i_bpOut_data[3:0];

wire bpIn_isPanic = bpIn_isRep && bpIn_rep_panic;
wire bpOut_isPanic = bpOut_isRep && bpOut_rep_panic;

wire bpIn_singleByteReq = bpIn_isReq && bpIn_req_read && bpIn_req_prevAddr;
wire bpOut_singleByteReq = bpOut_isReq && bpOut_req_read && bpOut_req_prevAddr;

wire bpIn_isEop;
wire bpOut_isEop;

`dff_cg_srst(reg [4:0], bpIn_nBytesRcvd, i_clk, bpIn_accepted, i_rst, '0)
always @*
  if (bpIn_isEop)
    bpIn_nBytesRcvd_d = '0;
  else
    bpIn_nBytesRcvd_d = bpIn_nBytesRcvd_q + 1;

`dff_cg_srst(reg [4:0], bpOut_nBytesSent, i_clk, bpOut_accepted, i_rst, '0)
always @*
  if (bpOut_isEop)
    bpOut_nBytesSent_d = '0;
  else
    bpOut_nBytesSent_d = bpOut_nBytesSent_q + 1;

assign bpIn_isHdr = bpIn_accepted && (bpIn_nBytesRcvd_q == '0);
assign bpOut_isHdr = bpOut_accepted && (bpOut_nBytesSent_q == '0);

// Store number of bytes in packet, to detect when should stop accepting and
// the AXI transaction may begin.
`dff_cg_srst(reg [4:0], bpIn_nBytesPkt, i_clk, bpIn_isHdr, i_rst, '0)
always @*
  if (bpIn_isPanic)
    bpIn_nBytesPkt_d = 1;                          // reply, panic
  else if (bpIn_isReq)
    if (bpIn_req_read)
      if (bpIn_req_prevAddr)
        bpIn_nBytesPkt_d = 1;                      // read, no address
      else
        bpIn_nBytesPkt_d = 1 + ADDR_BYTEW;         // read, with address
    else // bpIn_req_write
      if (bpIn_req_prevAddr)
        bpIn_nBytesPkt_d = 1 + bpIn_req_nBytes;    // write, no address
      else
        bpIn_nBytesPkt_d = 1 + ADDR_BYTEW + bpIn_req_nBytes;// write, with address
  else
    bpIn_nBytesPkt_d = '1; // Unsupported case, non-panic reply maybe with data

`dff_cg_srst(reg [4:0], bpIn_nBytesResp, i_clk, bpIn_isReq, i_rst, '0)
always @*
  if (bpIn_isReq)
    if (bpIn_req_read)
      bpIn_nBytesResp_d = 1 + bpIn_req_nBytes;  // header, read reply data
    else
      bpIn_nBytesResp_d = 1;                    // header only, write ack
  else
    bpIn_nBytesResp_d = '0;                     // No response to reply

// Store number of bytes in reply packet.
// NOTE: Checker supports more than design.
`dff_cg_srst(reg [4:0], bpOut_nBytesPkt, i_clk, bpOut_isHdr, i_rst, '0)
always @*
  if (bpOut_isPanic)
    bpOut_nBytesPkt_d = 1;                         // reply, panic
  else if (bpOut_isRep)
    bpOut_nBytesPkt_d = bpIn_nBytesResp_q;         // reply, write ack or read data
  else // bpOut_isReq
    if (bpOut_req_read)
      if (bpOut_req_prevAddr)
        bpOut_nBytesPkt_d = 1;                     // read, no address
      else
        bpOut_nBytesPkt_d = 1 + ADDR_BYTEW;        // read, with address
    else // bpOut_req_write
      if (bpOut_req_prevAddr)
        bpOut_nBytesPkt_d = 1 + bpOut_req_nBytes;  // write, no address
      else
        bpOut_nBytesPkt_d = 1 + ADDR_BYTEW + bpOut_req_nBytes;// write, with address

wire [4:0] nBytesPktMax = (5'd1+ADDR_BYTEW+5'd8);

// Same cycle as last byte of packet.
assign bpIn_isEop = bpIn_accepted &&
  (bpIn_singleByteReq || // Single-byte request - read with no address
   bpIn_isPanic ||  // Single-byte reply - panic
   ((bpIn_nBytesRcvd_q != '0) && // Multi-byte
    (bpIn_nBytesPkt_q == (bpIn_nBytesRcvd_q+1))));

assign bpOut_isEop = bpOut_accepted &&
  (bpOut_singleByteReq || // Single-byte request - read with no address
   (bpIn_nBytesResp_q == 1) ||  // Single-byte reply - panic, or write ack
   ((bpOut_nBytesSent_q != '0) && // Multi-byte
    (bpOut_nBytesPkt_q == (bpOut_nBytesSent_q+1))));

// }}} support logic

// {{{ synthable properties

// Driver should only use sane values for nBytes.
`asrt(bpIn_req_nBytes_onehot0, i_clk, !i_rst && bpIn_isReq, $onehot0(bpIn_req_nBytes))

// Driver should only use supported packet types.
`asrt(bpIn_nBytesPkt, i_clk, !i_rst, nBytesPktMax >= bpIn_nBytesPkt_q)

// Single outstanding BytePipe transaction -->
//  AXI read/write request channels should never operate concurrently.
//  AXI read/write reply channels should never operate concurrently.
`asrt(axiSend_onehot0, i_clk, !i_rst, $onehot0({axiAR_accepted, axiAW_accepted}))
`asrt(axiRecv_onehot0, i_clk, !i_rst, $onehot0({axiR_accepted, axiB_accepted}))

/* invalid: AW and W channels are actually one channel for AXI4lite.
wire a_axiAW_with_W =
  (i_axi_AWREADY == i_axi_WREADY) &&
  (i_axi_AWVALID == i_axi_WVALID) &&
  (axiAW_accepted == axiW_accepted);
`asrtw_en(a_axiAW_with_W, i_clk, !i_rst)
*/

// No AXI activity while receiving a BytePipe packet.
`asrt(axiIdleDuringRecvPkt0, i_clk, !i_rst && (bpIn_nBytesRcvd_q != '0), !axiAny_accepted)
`asrt(axiIdleDuringRecvPkt1, i_clk, !i_rst, !(bpIn_accepted && axiAny_accepted))

// No AXI activity while sending a BytePipe packet.
`asrt(axiIdleDuringSendPkt0, i_clk, !i_rst && (bpOut_nBytesSent_q != '0), !axiAny_accepted)
`asrt(axiIdleDuringSendPkt1, i_clk, !i_rst, !(bpOut_accepted && axiAny_accepted))

// }}} synthable properties

endmodule
