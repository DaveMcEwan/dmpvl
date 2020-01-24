`include "dff.vh"

// Driver for bpAxiMaster_tb.
module driveBpPacket (
  input  wire                       i_clk,
  input  wire                       i_rst,

  input  wire                       i_ready,
  output wire                       o_valid,

  // Read reply nBytes is not part of packet since the receiver should be
  // expecting a partictular number.
  output wire [3:0]                 o_repOnly_nBytes,

  output wire                       o_repNotReq,
  output wire [63:0]                o_data,
  output wire [63:0]                o_addr,

  output wire                       o_req_readNotWrite,
  output wire                       o_req_incrAddr,
  output wire                       o_req_prevAddr,
  output wire [3:0]                 o_req_nBytes,

  output wire [1:0]                 o_rep_resp,
  output wire                       o_rep_panic,
  output wire [3:0]                 o_rep_hint
);

reg [3:0]   rnd_o_repOnly_nBytes;

reg         rnd_o_repNotReq;
reg [63:0]  rnd_o_data;
reg [63:0]  rnd_o_addr;

reg         rnd_o_req_readNotWrite;
reg         rnd_o_req_incrAddr;
reg         rnd_o_req_prevAddr;
reg [3:0]   rnd_o_req_nBytes;

reg [1:0]   rnd_o_rep_resp;
reg         rnd_o_rep_panic;
reg [3:0]   rnd_o_rep_hint;

reg [3:0]   dnCntr_o_valid;

wire drv_accepted = i_ready && o_valid;

`dff_nocg_norst(reg [31:0], dnCntr_o_valid, i_clk)
initial dnCntr_o_valid_q = '0;
always @*
  if (drv_accepted)
    dnCntr_o_valid_d = $urandom_range(15, 0);
  else if (dnCntr_o_valid_q != '0)
    dnCntr_o_valid_d = dnCntr_o_valid_q - 1;
  else
    dnCntr_o_valid_d = dnCntr_o_valid_q;

assign o_valid = (dnCntr_o_valid_q == '0);

// Send PANIC first.
`dff_nocg_srst(reg, doPanic, i_clk, i_rst, 1'b1)
always @*
  if (drv_accepted)
    doPanic_d = 1'b0;
  else
    doPanic_d = doPanic_q;


always @(posedge i_clk)
  if (doPanic_d) begin
    rnd_o_repOnly_nBytes    = '0;

    rnd_o_repNotReq         = 1'b1;
    rnd_o_data              = 'x;
    rnd_o_addr              = 'x;

    rnd_o_req_readNotWrite  = 'x;
    rnd_o_req_incrAddr      = 'x;
    rnd_o_req_prevAddr      = 'x;
    rnd_o_req_nBytes        = 'x;

    rnd_o_rep_resp          = '1;
    rnd_o_rep_panic         = 1'b1;
    rnd_o_rep_hint          = '1;
  end
  else if (drv_accepted) begin
    rnd_o_repOnly_nBytes    = (1 << $urandom_range(3, 0));

    //rnd_o_repNotReq         = ($urandom_range(3, 0) == 'd0); // 3/4 request, 1/4 reply
    rnd_o_repNotReq         = 1'b0; // request-only
    rnd_o_data              = {$urandom, $urandom};
    rnd_o_addr              = {$urandom, $urandom};

    rnd_o_req_readNotWrite  = $urandom_range(1, 0);
    rnd_o_req_incrAddr      = $urandom_range(1, 0);
    rnd_o_req_prevAddr      = $urandom_range(1, 0);
    rnd_o_req_nBytes        = (1 << $urandom_range(3, 0));

    rnd_o_rep_resp          = $urandom_range(3, 0);
    rnd_o_rep_panic         = ($urandom_range(63, 0) == 'd0);
    rnd_o_rep_hint          = $urandom_range(15, 0);
  end

assign o_repOnly_nBytes = rnd_o_repOnly_nBytes;

assign o_repNotReq = rnd_o_repNotReq;
assign o_data = rnd_o_data;
assign o_addr = rnd_o_addr;

assign o_req_readNotWrite = rnd_o_req_readNotWrite;
assign o_req_incrAddr     = rnd_o_req_incrAddr;
assign o_req_prevAddr     = rnd_o_req_prevAddr;
assign o_req_nBytes       = rnd_o_req_nBytes;

assign o_rep_resp   = rnd_o_rep_resp;
assign o_rep_panic  = rnd_o_rep_panic;
assign o_rep_hint   = rnd_o_rep_hint;

endmodule
