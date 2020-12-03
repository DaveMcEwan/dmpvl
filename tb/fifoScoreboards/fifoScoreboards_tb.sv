`include "misc.svh"

/** fifoW1R1_tb
 * Instance multiple fifos with different parameters.
 * Instance name should be u_fifo_<WIDTH>_<DEPTH>_(mem|flops)
 * Connecting wires should be <instance>_<port>
 */
module fifoW1R1_tb (
  input  wire           i_clk,
  input  wire           i_rst

);

wire i_wrst = i_rst;
wire i_rrst = i_rst;

// Clockgates drop between 1/20 and 1/(CGGATE_CTRL_C * 2**CGRATE_CTRL_A).
// Rates changes around every 2**CGRATE_CTRL_B cycles.
// ==> Clockgates drop between 1/20 and 1/640 cycles, with actual rate changing
//     roughly every 64ki cycles.
localparam CGGATE_CTRL_A = 5;
localparam CGGATE_CTRL_B = 16;
localparam CGGATE_CTRL_C = 20;
reg [CGGATE_CTRL_A-1:0] wcgRate, rcgRate;
initial begin
  wcgRate = 5;
  rcgRate = 5;
end
always @(posedge i_clk) begin
  if ($random % (1 << CGGATE_CTRL_B) == 0) wcgRate = $random;
  if ($random % (1 << CGGATE_CTRL_B) == 0) rcgRate = $random;
end

// Handshake/flow-controls pulse between 1/1 and 1/2**FLOWRATE_CTRL_A.
// Rates changes around every 2**FLOWRATE_CTRL_B cycles.
// ==> Flow-controls pulse between 1/1 and 1/8 cycles, with actual rate changing
//     roughly every 512 cycles.
localparam FLOWRATE_CTRL_A = 3;
localparam FLOWRATE_CTRL_B = 9;
reg [FLOWRATE_CTRL_A-1:0] wvalidRate, rreadyRate;
initial begin
  wvalidRate = 5;
  rreadyRate = 5;
end
always @(posedge i_clk) begin
  if ($random % (1 << FLOWRATE_CTRL_B) == 0) wvalidRate = $random;
  if ($random % (1 << FLOWRATE_CTRL_B) == 0) rreadyRate = $random;
end

reg i_wcg, i_rcg;
reg [31:0] i_wdata;
reg i_wvalid, i_rready;
always @(posedge i_clk) begin
  i_wcg    <= ($random % ((wcgRate+1) * CGGATE_CTRL_C)) != 0;
  i_rcg    <= ($random % ((rcgRate+1) * CGGATE_CTRL_C)) != 0;
  i_wdata  <= $random;
  i_wvalid <= ($random % (wvalidRate+1)) == 0;
  i_rready <= ($random % (rreadyRate+1)) == 0;
end

wire o_wready;
wire [`WIDTH-1:0] o_rdata;
wire o_rvalid;

generate if (`STRING(`DUT_TYPE) == "fifoW1R1") begin
`ifdef FIFO_W1R1
  fifoW1R1 #(
    .WIDTH              (`WIDTH),
    .DEPTH              (`DEPTH),
    .FLOPS_NOT_MEM      (`FLOPS_NOT_MEM),
    .FORCEKEEP_NENTRIES (`FORCEKEEP_NENTRIES),
  ) u_dut (
    // NOTE: Single clock domain could use either i_wclk or i_rclk;
    .i_clk      (i_wclk),
    .i_rst      (i_wrst),
    .i_cg       (i_wcg),

    .i_flush    (1'b0),

    .i_data     (i_wdata[`WIDTH-1:0]),
    .i_valid    (i_wvalid),
    .o_ready    (o_wready),

    .o_data     (o_rdata),
    .o_valid    (o_rvalid),
    .i_ready    (i_rready),

    .o_pushed   (),
    .o_popped   (),

    .o_wptr     (),
    .o_rptr     (),

    .o_validEntries (),
    .o_nEntries     (),

    .o_entries  ()
  );
end else if (`STRING(`DUT_TYPE) == "cdcData") begin
  cdcData #(
    .WIDTH          (`WIDTH),
    .TOPOLOGY       (`TOPOLOGY),
    .FLOPS_NOT_MEM  (`FLOPS_NOT_MEM)
  ) u_dut (
    .i_wclk     (i_wclk),
    .i_wrst     (i_wrst),
    .i_wcg      (i_wcg),

    .i_rclk     (i_rclk),
    .i_rrst     (i_rrst),
    .i_rcg      (i_rcg),

    .i_wdata    (i_wdata[`WIDTH-1:0]),
    .i_wvalid   (i_wvalid),
    .o_wready   (o_wready),

    .o_rdata    (o_rdata),
    .o_rvalid   (o_rvalid),
    .i_rready   (i_rready)
  );
end else if (`STRING(`DUT_TYPE) == "cdcFifo") begin
  cdcFifo #(
    .WIDTH          (`WIDTH),
    .DEPTH          (`DEPTH),
    .FLOPS_NOT_MEM  (`FLOPS_NOT_MEM)
    .FAST_NOT_SMALL (`FAST_NOT_SMALL)
  ) u_dut (
    .i_wclk     (i_wclk),
    .i_wrst     (i_wrst),
    .i_wcg      (i_wcg),

    .i_rclk     (i_rclk),
    .i_rrst     (i_rrst),
    .i_rcg      (i_rcg),

    .i_wdata    (i_wdata[`WIDTH-1:0]),
    .i_wvalid   (i_wvalid),
    .o_wready   (o_wready),

    .o_rdata    (o_rdata),
    .o_rvalid   (o_rvalid),
    .i_rready   (i_rready)

    .o_wptr     (),
    .o_rptr     (),

    .o_wpushed  (),
    .o_rpopped  ()
  );
end endgenerate

endmodule
