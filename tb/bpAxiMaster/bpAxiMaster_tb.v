/** bpAxiMaster_tb.sv - Testbench for bpAxiMaster
 */
module bpAxiMaster_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  `error No Verilator testbench here!
  input wire i_rootClk,
`endif
);

localparam ADDR_BYTEW_11 = 1;
localparam DATA_BYTEW_11 = 1;
localparam AXI_ID_W_11 = 1;

wire [AXI_ID_W_11-1:0]        axi11_awid;
wire [8*ADDR_BYTEW_11-1:0]    axi11_awaddr;
wire [2:0]                    axi11_awprot;
wire                          axi11_awvalid;
wire                          axi11_awready;
wire [8*DATA_BYTEW_11-1:0]    axi11_wdata;
wire [DATA_BYTEW_11-1:0]      axi11_wstrb;
wire                          axi11_wvalid;
wire                          axi11_wready;
wire [AXI_ID_W_11-1:0]        axi11_bid;
wire [1:0]                    axi11_bresp;
wire                          axi11_bvalid;
wire                          axi11_bready;
wire [AXI_ID_W_11-1:0]        axi11_arid;
wire [8*ADDR_BYTEW_11-1:0]    axi11_araddr;
wire [2:0]                    axi11_arprot;
wire                          axi11_arvalid;
wire                          axi11_arready;
wire [AXI_ID_W_11-1:0]        axi11_rid;
wire [8*DATA_BYTEW_11-1:0]    axi11_rdata;
wire [1:0]                    axi11_rresp;
wire                          axi11_rvalid;
wire                          axi11_rready;

wire [7:0]  bpIn_data;
wire        bpIn_valid;
wire        bpIn_ready;

// TODO: Check bpOut_data,bpOut_valid.
wire [7:0]  bpOut_data;
wire        bpOut_valid;
wire        bpOut_ready;

// TODO: Drive send11_*.
wire                       send11_o_ready;
wire                       send11_i_valid;
wire [3:0]                 send11_i_repOnly_nBytes;
wire                       send11_i_repNotReq;
wire [63:0]                send11_i_data;
wire [63:0]                send11_i_addr;
wire                       send11_i_req_readNotWrite;
wire                       send11_i_req_incrAddr;
wire                       send11_i_req_prevAddr;
wire [3:0]                 send11_i_req_nBytes;
wire [1:0]                 send11_i_rep_resp;
wire                       send11_i_rep_panic;
wire [3:0]                 send11_i_rep_hint;

wire slv_o_busy;
wire slv_o_idle;
wire slv_o_stall;

wire clk;
reg rst;

`ifndef VERILATOR // {{{ Non-V_erilator tb

initial begin
  $dumpfile("build/bpAxiMaster_tb.iverilog.vcd");
  $dumpvars(0, bpAxiMaster_tb);
end

driveBpPacket v_driveBpPacket_11 ( // {{{
  .i_clk                    (clk),
  .i_rst                    (rst),

  .i_ready                  (send11_o_ready),
  .o_valid                  (send11_i_valid),

  .o_repOnly_nBytes         (send11_i_repOnly_nBytes),

  .o_repNotReq              (send11_i_repNotReq),
  .o_data                   (send11_i_data),
  .o_addr                   (send11_i_addr),

  .o_req_readNotWrite       (send11_i_req_readNotWrite),
  .o_req_incrAddr           (send11_i_req_incrAddr),
  .o_req_prevAddr           (send11_i_req_prevAddr),
  .o_req_nBytes             (send11_i_req_nBytes),

  .o_rep_resp               (send11_i_rep_resp),
  .o_rep_panic              (send11_i_rep_panic),
  .o_rep_hint               (send11_i_rep_hint)
); // }}} v_driveBpPacket_11

`endif // }}} Non-V_erilator tb


generateClock u_clk (
`ifdef VERILATOR // V_erilator must drive its own root clock
  .i_rootClk        (i_rootClk),
`endif
  .o_clk            (clk),
  .i_periodHi       (8'd0),
  .i_periodLo       (8'd0),
  .i_jitterControl  (8'd0)
);

`dff_nocg_norst(reg [31:0], nCycles, clk)
initial nCycles_q = '0;
always @*
  nCycles_d = nCycles_q + 'd1;

always @*
  if (nCycles_q > 5)
    rst = 1'b0;
  else
    rst = 1'b1;

`dff_nocg_srst(reg [31:0], nTxns, clk, rst, '0)
always @*
  if (send11_o_ready && send11_i_valid)
    nTxns_d = nTxns_q + 1;
  else
    nTxns_d = nTxns_q;

// Finish sim after an upper limit on the number of clock cycles, or BytePipe
// transactions sent.
always @*
  if ((nCycles_q > 100000) || (nTxns_q > 10000))
    $finish;

// Randomly drop bpOut_ready 1/8 of cycles.
reg [2:0] rnd_bpOut_ready;
always @(posedge clk)
  rnd_bpOut_ready = $random;
assign bpOut_ready = rnd_bpOut_ready == 3'b0;

checkBpToAxi #( // {{{ v_checkBpToAxi_11
  .ADDR_BYTEW   (ADDR_BYTEW_11), // in {1..8}. Affects both AXI interface and BytePipe protocol.
  .DATA_BYTEW   (DATA_BYTEW_11), // in {1,2,4,8}. AXI only.
  .AXI_ID_W     (AXI_ID_W_11)    // AXI only.
) v_checkBpToAxi_11 (
  .i_clk              (clk),
  .i_rst              (rst),

  .i_axi_AWID         (axi11_awid),
  .i_axi_AWADDR       (axi11_awaddr),
  .i_axi_AWPROT       (axi11_awprot),
  .i_axi_AWVALID      (axi11_awvalid),
  .i_axi_AWREADY      (axi11_awready),

  // Write data channel.
  .i_axi_WDATA        (axi11_wdata),
  .i_axi_WSTRB        (axi11_wstrb),
  .i_axi_WVALID       (axi11_wvalid),
  .i_axi_WREADY       (axi11_wready),

  // Write response channel.
  .i_axi_BID          (axi11_bid),
  .i_axi_BRESP        (axi11_bresp),
  .i_axi_BVALID       (axi11_bvalid),
  .i_axi_BREADY       (axi11_bready),

  // Read address channel.
  .i_axi_ARID         (axi11_arid),
  .i_axi_ARADDR       (axi11_araddr),
  .i_axi_ARPROT       (axi11_arprot),
  .i_axi_ARVALID      (axi11_arvalid),
  .i_axi_ARREADY      (axi11_arready),

  // Read data channel.
  .i_axi_RID          (axi11_rid),
  .i_axi_RDATA        (axi11_rdata),
  .i_axi_RRESP        (axi11_rresp),
  .i_axi_RVALID       (axi11_rvalid),
  .i_axi_RREADY       (axi11_rready),

  // Request
  .i_bpIn_data        (bpIn_data),
  .i_bpIn_valid       (bpIn_valid),
  .i_bpIn_ready       (bpIn_ready),

  // Reply
  .i_bpOut_data       (bpOut_data),
  .i_bpOut_valid      (bpOut_valid),
  .i_bpOut_ready      (bpOut_ready)
); // }}} v_checkBpToAxi_11

bpPacketSender #( // {{{ v_bpPacketSender_11
  .ADDR_BYTEW   (ADDR_BYTEW_11)  // in {1..8}. Affects both AXI interface and BytePipe protocol.
) v_bpPacketSender_11 (
  .i_clk                    (clk),
  .i_rst                    (rst),

  .o_ready                  (send11_o_ready),
  .i_valid                  (send11_i_valid),

  .i_repOnly_nBytes         (send11_i_repOnly_nBytes),

  .i_repNotReq              (send11_i_repNotReq),
  .i_data                   (send11_i_data),
  .i_addr                   (send11_i_addr),

  .i_req_readNotWrite       (send11_i_req_readNotWrite),
  .i_req_incrAddr           (send11_i_req_incrAddr),
  .i_req_prevAddr           (send11_i_req_prevAddr),
  .i_req_nBytes             (send11_i_req_nBytes),

  .i_rep_resp               (send11_i_rep_resp),
  .i_rep_panic              (send11_i_rep_panic),
  .i_rep_hint               (send11_i_rep_hint),

  // Outgoing BytePipe
  .o_bp_data                (bpIn_data),
  .o_bp_valid               (bpIn_valid),
  .i_bp_ready               (bpIn_ready)
); // }}} v_bpPacketSender_11

bpAxiMaster #( // {{{ bpAxiMaster_11
  .ADDR_BYTEW   (ADDR_BYTEW_11), // in {1..8}. Affects both AXI interface and BytePipe protocol.
  .DATA_BYTEW   (DATA_BYTEW_11), // in {1,2,4,8}. AXI only.
  .AXI_MST_ID   (0), // Constant ID for master.
  .AXI_ID_W     (AXI_ID_W_11)    // AXI only.
) u_bpAxiMaster_11 (
  .i_clk                    (clk),
  .i_rst                    (rst),

  // Signals ordered according to the document:
  // AMBA AXI and ACE Proctocol Specification
  // ARM IHI 0022D (ID102711)
  // IDs are included for interoperability with AXI4 (B1-124).

  // {{{ axi4lite master

  // Write address channel.
  .o_axiMst_AWID            (axi11_awid),
  .o_axiMst_AWADDR          (axi11_awaddr),
  .o_axiMst_AWPROT          (axi11_awprot), // unused
  .o_axiMst_AWVALID         (axi11_awvalid),
  .i_axiMst_AWREADY         (axi11_awready),

  // Write data channel.
  .o_axiMst_WDATA           (axi11_wdata),
  .o_axiMst_WSTRB           (axi11_wstrb),
  .o_axiMst_WVALID          (axi11_wvalid), // unused. Equal to o_axiMst_AWVALID.
  .i_axiMst_WREADY          (axi11_wready), // unused. Assumed equal to i_axiMst_AWREADY.

  // Write response channel.
  .i_axiMst_BID             (axi11_bid), // unused. Assumed compliant.
  .i_axiMst_BRESP           (axi11_bresp),
  .i_axiMst_BVALID          (axi11_bvalid),
  .o_axiMst_BREADY          (axi11_bready),

  // Read address channel.
  .o_axiMst_ARID            (axi11_arid),
  .o_axiMst_ARADDR          (axi11_araddr),
  .o_axiMst_ARPROT          (axi11_arprot), // unused
  .o_axiMst_ARVALID         (axi11_arvalid),
  .i_axiMst_ARREADY         (axi11_arready),

  // Read data channel.
  .i_axiMst_RID             (axi11_rid), // unused. Assumed compliant.
  .i_axiMst_RDATA           (axi11_rdata),
  .i_axiMst_RRESP           (axi11_rresp),
  .i_axiMst_RVALID          (axi11_rvalid),
  .o_axiMst_RREADY          (axi11_rready),

  // }}} axi4lite master

  // Incoming BytePipe
  .i_bp_data                (bpIn_data),
  .i_bp_valid               (bpIn_valid),
  .o_bp_ready               (bpIn_ready),

  // Outgoing BytePipe
  .o_bp_data                (bpOut_data),
  .o_bp_valid               (bpOut_valid),
  .i_bp_ready               (bpOut_ready)
); // }}} bpAxiMaster_11

axi4liteRandomSlave #( // {{{ axiSlave_11
  .IDLE_TIMEOUT         (3),
  .PROB_W               (8),
  .N_MEM_WORD           (256),
  .ADDR_BASE            (0),
  .ADDR_W               (8*ADDR_BYTEW_11),
  .DATA_BYTEW           (DATA_BYTEW_11),
  .ID_W                 (AXI_ID_W_11)
) v_axiSlave_11 (
  .i_clk                (clk),
  .i_rst                (rst),

  // Write address channel.
  .i_axi_AWID           (axi11_awid),
  .i_axi_AWADDR         (axi11_awaddr),
  .i_axi_AWPROT         (axi11_awprot),
  .i_axi_AWVALID        (axi11_awvalid),
  .o_axi_AWREADY        (axi11_awready),

  // Write data channel.
  .i_axi_WDATA          (axi11_wdata),
  .i_axi_WSTRB          (axi11_wstrb),
  .i_axi_WVALID         (axi11_wvalid),
  .o_axi_WREADY         (axi11_wready),

  // Write response channel.
  .o_axi_BID            (axi11_bid),
  .o_axi_BRESP          (axi11_bresp),
  .o_axi_BVALID         (axi11_bvalid),
  .i_axi_BREADY         (axi11_bready),

  // Read address channel.
  .i_axi_ARID           (axi11_arid),
  .i_axi_ARADDR         (axi11_araddr),
  .i_axi_ARPROT         (axi11_arprot),
  .i_axi_ARVALID        (axi11_arvalid),
  .o_axi_ARREADY        (axi11_arready),

  // Read data channel.
  .o_axi_RID            (axi11_rid),
  .o_axi_RDATA          (axi11_rdata),
  .o_axi_RRESP          (axi11_rresp),
  .o_axi_RVALID         (axi11_rvalid),
  .i_axi_RREADY         (axi11_rready),

  .i_pr_aw_stall        (8'd8),
  .i_pr_w_stall         (8'd16),
  .i_pr_b_stall         (8'd24),
  .i_pr_ar_stall        (8'd32),
  .i_pr_r_stall         (8'd40),
  .i_pr_bresp_notokay   (8'd48),
  .i_pr_rresp_notokay   (8'd56),
  .i_pr_rddata_corrupt  (8'd64),

  .o_busy               (slv_o_busy),
  .o_idle               (slv_o_idle),
  .o_stall              (slv_o_stall)
); // }}} axiSlave_11

endmodule

