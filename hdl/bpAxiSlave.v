`include "dff.vh"
// TODO: WIP, skeleton code only just now.

/* BytePipe to AXI4lite Slave
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
module bpAxiSlave #(
  parameter ADDR_BYTEW = 2, // in {1..8}. Affects both AXI interface and BytePipe protocol.
  parameter DATA_BYTEW = 4, // in {1,2,4,8}. AXI only.
  parameter AXI_MST_ID = 0, // Constant ID for master.
  parameter ID_W = 4        // AXI only.
) (
  input wire                        i_clk,
  input wire                        i_rst,

  // Signals ordered according to the document:
  // AMBA AXI and ACE Proctocol Specification
  // ARM IHI 0022D (ID102711)
  // IDs are included for interoperability with AXI4 (B1-124).

  // {{{ axi4lite slave

  // Write address channel signals.
  input  wire [ID_W-1:0]            i_axiSlv_AWID,
  input  wire [(8*ADDR_BYTEW)-1:0]  i_axiSlv_AWADDR,
  input  wire [2:0]                 i_axiSlv_AWPROT, // unused
  input  wire                       i_axiSlv_AWVALID,
  output wire                       o_axiSlv_AWREADY,

  // Write data channel signals.
  input  wire [(8*DATA_BYTEW)-1:0]  i_axiSlv_WDATA,
  input  wire [DATA_BYTEW-1:0]      i_axiSlv_WSTRB,
  input  wire                       i_axiSlv_WVALID, // unused. Assumed equal to i_axiSlv_AWVALID.
  output wire                       o_axiSlv_WREADY, // unused. Equal to o_axiSlv_AWREADY.

  // Write response channel signals.
  output wire [ID_W-1:0]            o_axiSlv_BID,
  output wire [1:0]                 o_axiSlv_BRESP,
  output wire                       o_axiSlv_BVALID,
  input  wire                       i_axiSlv_BREADY,

  // Read address channel signals.
  input  wire [ID_W-1:0]            i_axiSlv_ARID,
  input  wire [(8*ADDR_BYTEW)-1:0]  i_axiSlv_ARADDR,
  input  wire [2:0]                 i_axiSlv_ARPROT,
  input  wire                       i_axiSlv_ARVALID,
  output wire                       o_axiSlv_ARREADY,

  // Read data channel signals.
  output wire [ID_W-1:0]            o_axiSlv_RID,
  output wire [(8*DATA_BYTEW)-1:0]  o_axiSlv_RDATA,
  output wire [1:0]                 o_axiSlv_RRESP,
  output wire                       o_axiSlv_RVALID,
  input  wire                       i_axiSlv_RREADY,

  // }}} axi4lite slave

  // Incoming BHD
  input  wire [7:0]                 i_bp_data,
  input  wire                       i_bp_valid,
  output wire                       o_bp_ready,

  // Outgoing BHD
  output wire [7:0]                 o_bp_data,
  output wire                       o_bp_valid,
  input  wire                       i_bp_ready
);


genvar i;

wire bpIn_accepted = i_bp_valid && o_bp_ready;
wire bpOut_accepted = o_bp_valid && i_bp_ready;
wire axiAW_accepted = i_axiSlv_AWVALID && o_axiSlv_AWREADY;
wire axiAR_accepted = i_axiSlv_ARVALID && o_axiSlv_ARREADY;
wire axiB_accepted = o_axiSlv_BVALID && i_axiSlv_BREADY;
wire axiR_accepted = o_axiSlv_RVALID && i_axiSlv_RREADY;

wire bpIn_isEop;
`dff_cg_srst(reg [4:0], bpIn_nBytesRcvd, i_clk, bpIn_accepted, i_rst, '0)
always @*
  if (bpIn_isEop)
    bpIn_nBytesRcvd_d = '0;
  else
    bpIn_nBytesRcvd_d = bpIn_nBytesRcvd_q + 5'd1;

wire bpIn_isHdr = bpIn_accepted && (bpIn_nBytesRcvd_q == '0);

wire bpIn_isRep = bpInIsHeader && i_bp_data[7];
wire [1:0]  bpIn_rep_resp = i_bp_data[6:5];
wire        bpIn_rep_panic = bpIn_isRep && i_bp_data[4];
wire [3:0]  bpIn_rep_hint = i_bp_data[3:0];

`dff_cg_srst(reg [4:0], bpIn_nBytesRemaining, i_clk, bpIn_accepted, i_rst, '0)
always @*
  if (bpIn_isRep && !bpIn_rep_panic)                // read with data, or write ack
    bpIn_nBytesRemaining_d = bpIn_nBytesExpected_q;
  else if (bpIn_nBytesRemaining_q != '0)
    bpIn_nBytesRemaining_d = bpIn_nBytesRemaining_q - 5'd1;
  else
    bpIn_nBytesRemaining_d = bpIn_nBytesRemaining_q;

assign bpIn_isEop =
  bpIn_accepted &&
  (bpIn_nBytesRcvd_q != '0) &&
  (bpIn_nBytesRemaining_q == 5'd1);

endmodule
