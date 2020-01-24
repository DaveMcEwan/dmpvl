`include "asrt.vh"
`include "dff.vh"

/* BytePipe
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
*/
module bpPacketSender #(
  parameter ADDR_BYTEW = 2  // in {1..8}. Affects BytePipe protocol.
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  output wire                       o_ready,
  input  wire                       i_valid,

  // Read reply nBytes is not part of packet since the receiver should be
  // expecting a partictular number.
  input  wire [3:0]                 i_repOnly_nBytes,

  input  wire                       i_repNotReq,
  input  wire [63:0]                i_data,
  input  wire [63:0]                i_addr,

  input  wire                       i_req_readNotWrite,
  input  wire                       i_req_incrAddr,
  input  wire                       i_req_prevAddr,
  input  wire [3:0]                 i_req_nBytes,

  input  wire [1:0]                 i_rep_resp,
  input  wire                       i_rep_panic,
  input  wire [3:0]                 i_rep_hint,

  // Outgoing BytePipe
  output wire [7:0]                 o_bp_data,
  output wire                       o_bp_valid,
  input  wire                       i_bp_ready
);

wire drv_accepted = i_valid && o_ready;
wire bp_accepted = o_bp_valid && i_bp_ready;

// Delayed version just for assumptions.
`dff_nocg_norst_d(reg, drv_accepted, i_clk, drv_accepted)

// Should not accept new input from driver while a packet is in progress.
`asrt(drv_bp_onehot0, i_clk, !i_rst, $onehot0({drv_accepted, bp_accepted}))

// Accept and store inputs.
`dff_cg_norst_d(reg [3:0],  repOnly_nBytes,   i_clk, drv_accepted, i_repOnly_nBytes)
`dff_cg_norst_d(reg,        repNotReq,        i_clk, drv_accepted, i_repNotReq)
`dff_cg_norst_d(reg [63:0], data,             i_clk, drv_accepted, i_data)
`dff_cg_norst_d(reg [63:0], addr,             i_clk, drv_accepted, i_addr)
`dff_cg_norst_d(reg,        req_readNotWrite, i_clk, drv_accepted, i_req_readNotWrite)
`dff_cg_norst_d(reg,        req_incrAddr,     i_clk, drv_accepted, i_req_incrAddr)
`dff_cg_norst_d(reg,        req_prevAddr,     i_clk, drv_accepted, i_req_prevAddr)
`dff_cg_norst_d(reg [3:0],  req_nBytes,       i_clk, drv_accepted, i_req_nBytes)
`dff_cg_norst_d(reg [1:0],  rep_resp,         i_clk, drv_accepted, i_rep_resp)
`dff_cg_norst_d(reg,        rep_panic,        i_clk, drv_accepted, i_rep_panic)
`dff_cg_norst_d(reg [3:0],  rep_hint,         i_clk, drv_accepted, i_rep_hint)

// Requests must have sane values for nBytes.
`asrt(req_nBytes_onehot, i_clk, !i_rst && drv_accepted_q && !repNotReq_q, $onehot(req_nBytes_q))

// Immediately calculate and store packet size.
`dff_cg_srst(reg [4:0], nBytesPkt, i_clk, drv_accepted, i_rst, '0)
always @*
  if (i_repNotReq && i_rep_panic)
    nBytesPkt_d = 1; // header(reply), no data with panic
  else if (i_repNotReq)
    nBytesPkt_d = i_repOnly_nBytes + 1; // header(reply), read-data
  else
    if (i_req_readNotWrite)
      if (i_req_prevAddr)
        nBytesPkt_d = 1; // header(read), no address
      else
        nBytesPkt_d = ADDR_BYTEW + 1; // header(read), address
    else
      if (i_req_prevAddr)
        nBytesPkt_d = i_req_nBytes + 1; // header(write), no address, write-data
      else
        nBytesPkt_d = i_req_nBytes + ADDR_BYTEW + 1; // header(write), address, write-data

`dff_nocg_srst(reg [4:0], nBytesSent, i_clk, i_rst, '0)
always @*
  if (drv_accepted)
    nBytesSent_d = '0;
  else if (bp_accepted)
    nBytesSent_d = nBytesSent_q + 1;
  else
    nBytesSent_d = nBytesSent_q;

wire isHdr = bp_accepted && (nBytesSent_q == '0);
wire isEop = bp_accepted && ((nBytesSent_q+1) == nBytesPkt_q);

wire [7:0] hdrRequest = {1'b0, i_req_readNotWrite, i_req_prevAddr, i_req_incrAddr, i_req_nBytes};
wire [7:0] hdrReply = {1'b1, i_rep_resp, i_rep_panic, i_rep_hint};

`dff_cg_norst(reg [7:0], bp_data, i_clk, (drv_accepted || bp_accepted))
always @*
  if (drv_accepted)
    bp_data_d = i_repNotReq ? hdrReply : hdrRequest; // header
  else if (bp_accepted)
    if (repNotReq_q) // Reply data immediately follows header.
        bp_data_d = i_data[8*(nBytesSent_q) +: 8];
    else
      if (req_prevAddr_q) // No address so straight to write data. Reads will terminate first.
        bp_data_d = i_data[8*(nBytesSent_q) +: 8];
      else if (nBytesSent_q < ADDR_BYTEW) // Address phase.
        bp_data_d = i_addr[8*(nBytesSent_q) +: 8];
      else // Data phase after address.
        bp_data_d = i_data[8*(nBytesSent_q-ADDR_BYTEW) +: 8];

assign o_bp_data = bp_data_q;
assign o_bp_valid = (nBytesPkt_q > nBytesSent_q);

assign o_ready = !o_bp_valid;

endmodule
