`include "dff.svh"
`include "asrt.svh"
`include "misc.svh"

module usbfsEndpRx #(
  parameter MAX_PKT = 8
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  input  wire                       i_ready,
  output wire                       o_valid,
  output wire [7:0]                 o_data,

  // Host-to-device
  output wire                       o_erReady,
  input  wire                       i_erValid,
  output wire                       o_erStall,

  // Read buffer interface to u_rx
  output wire                         o_erRdEn,
  output wire [$clog2(MAX_PKT)-1:0]   o_erRdIdx,
  input  wire [7:0]                   i_erRdByte,
  input  wire [$clog2(MAX_PKT+1)-1:0] i_erRdNBytes
);

localparam NBYTES_W = $clog2(MAX_PKT + 1);
localparam IDX_W = $clog2(MAX_PKT);

wire accepted = i_ready && o_valid;
wire er_accepted = o_erReady && i_erValid;

// NOTE: Relies on USB wire speed being much slower than clock.
// Transactor will reject packet, forcing host to retransmit, if this fifo is
// not able to accept a full packet.
// Minimum time from one data packet to the next is at least another token
// (32b * 4cycles/b = 128 cycles) so there's plenty of time to take the payload
// even with MAX_PKT=64.
`dff_cg_srst_d(reg [NBYTES_W-1:0], rdNBytes, i_clk, er_accepted, i_rst, '0, i_erRdNBytes)
`dff_nocg_srst(reg [NBYTES_W-1:0], rdIdx, i_clk, i_rst || er_accepted, '0)
always @* rdIdx_d = o_erRdEn ? (rdIdx_q + 'd1) : rdIdx_q;

assign o_erRdIdx = rdIdx_q`LSb(IDX_W);
assign o_erRdEn = (rdNBytes_q != rdIdx_q);

`dff_nocg_srst_d(reg, push, i_clk, i_rst, 1'b0, o_erRdEn)

// {{{ fifo
fifo #(
  .WIDTH          (8),
  .DEPTH          (MAX_PKT),
  .FLOPS_NOT_MEM  (0)
) u_fifo (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (1'b1),

  .i_flush    (1'b0), // unused

  .i_data     (i_erRdByte),
  .i_valid    (push_q),
  .o_ready    (),

  .o_data     (o_data),
  .o_valid    (o_valid),
  .i_ready    (accepted),

  .o_pushed   (),
  .o_popped   (),

  .o_wrptr    (), // unused
  .o_rdptr    (), // unused

  .o_validEntries (), // unused
  .o_nEntries     (), // unused

  .o_entries  ()  // unused
);
// }}} fifo

// Must have space for a full packet.
assign o_erReady = !o_valid;

// There are no halting conditions.
assign o_erStall = 1'b0;

endmodule
