`include "dff.svh"

// Drive random transactions to/from usbFullSpeedTransactor.
// No attempt made at transaction level protocol compliance as this is just to
// stress the transaction logic.
module driveTransactions (
  input  wire                       i_clk,
  input  wire                       i_rst,

  input  wire                       i_ready,
  output wire                       o_valid,

  output wire [2:0]                 o_txnType,
  output wire [6:0]                 o_txnAddr,
  output wire [3:0]                 o_txnEndp
);

`include "usbSpec.svh"

wire accepted = i_ready && o_valid;
`dff_nocg_srst(reg [31:0], nTxns, i_clk, i_rst, '0)
always @*
  if (accepted)
    nTxns_d = nTxns_q + 1;
  else
    nTxns_d = nTxns_q;

// Randomly drop o_valid for 7/8 of cycles.
reg [2:0] rnd_valid;
`ifndef VERILATOR
always @(posedge i_clk)
  rnd_valid = $urandom_range(7, 0);
`endif
assign o_valid = !i_rst && (rnd_valid == 3'b0);

// {SETUP, OUT, IN}
// Do SETUPs before any OUTs or INs.
`dff_nocg_srst(reg [2:0], txnType, i_clk, i_rst, 3'b100)
`ifndef VERILATOR
always @*
  if (nTxns_q < 5)
    txnType_d = 3'b100;
  else if (nTxns_q < 10)
    txnType_d = 3'b010;
  else if (nTxns_q < 15)
    txnType_d = 3'b001;
  else
    txnType_d = 1 << $urandom_range(2, 0);
`endif
assign o_txnType = txnType_q;

// TODO
assign o_txnAddr = 7'd0;
assign o_txnEndp = 4'd0;

endmodule
