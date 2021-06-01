`include "dff.svh"

`ifndef N_CYCLES
`define N_CYCLES 'd100
`endif

module praxi_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire   i_clk,
  input  wire   i_rst
`endif
);

// {{{ clock,clockgate,reset,dump

wire clk;
//reg cg;
reg rst;

generateClock u_clk (
`ifdef VERILATOR // V_erilator must drive its own root clock
  .i_rootClk        (i_clk),
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

//initial cg = 1'b1;
`ifdef VERILATOR // V_erilator tb drives its own clockgate,reset
//always @* cg = i_cg;
always @* rst = i_rst;
`else
//always @(posedge clk) cg = ($urandom_range(9, 0) != 0); // TODO: Dynamic cg.

initial rst = 1'b1;
always @*
  if (nCycles_q > 20)
    rst = 1'b0;
  else
    rst = 1'b1;

initial begin
  $dumpfile("build/praxi_tb.iverilog.vcd");
  $dumpvars(0, praxi_tb);
end

// Finish sim after an upper limit on the number of clock cycles.
always @* if (nCycles_q > `N_CYCLES) $finish;
`endif

// }}} clock,clockgate,reset,dump

localparam PROB_W = 8;
localparam AXI_ADDR_W = 16;
localparam AXI_DATA_BYTEW = 4;
localparam AXI_DATA_W = AXI_DATA_BYTEW*8;
localparam AXI_ID_W = 4;
localparam AXI_N_PAGEWORDS = (1<<10);
localparam AXI_SLV0_ADDR_BASE = 'hcafe0000;

localparam OFFSET_W = 10;
localparam OFFSET_L = 2;
localparam OFFSET_H = OFFSET_W + OFFSET_L - 1; // 11
localparam PAGENUM_L = OFFSET_H + 1;
localparam PAGENUM_H = AXI_ADDR_W - 1;
localparam PAGENUM_W = PAGENUM_H - PAGENUM_L + 1;

// {{{ declarations

// AXI4lite connections.
wire [AXI_ID_W-1:0]     axi_awid;
wire [AXI_ADDR_W-1:0]   axi_awaddr;
wire [2:0]              axi_awprot;
wire                    axi_awvalid;
wire                    axi_awready;
wire [AXI_DATA_W-1:0]   axi_wdata;
wire [3:0]              axi_wstrb;
wire                    axi_wvalid;
wire                    axi_wready;
wire [AXI_ID_W-1:0]     axi_bid;
wire [1:0]              axi_bresp;
wire                    axi_bvalid;
wire                    axi_bready;
wire [AXI_ID_W-1:0]     axi_arid;
wire [AXI_ADDR_W-1:0]   axi_araddr;
wire [2:0]              axi_arprot;
wire                    axi_arvalid;
wire                    axi_arready;
wire [AXI_ID_W-1:0]     axi_rid;
wire [AXI_DATA_W-1:0]   axi_rdata;
wire [1:0]              axi_rresp;
wire                    axi_rvalid;
wire                    axi_rready;

// Monitor outputs
wire                    mon_aw_tfr;
wire                    mon_w_tfr;
wire                    mon_b_tfr;
wire                    mon_ar_tfr;
wire                    mon_r_tfr;
wire                    mon_b_decerr;
wire                    mon_b_slverr;
wire                    mon_b_okay;
wire                    mon_r_decerr;
wire                    mon_r_slverr;
wire                    mon_r_okay;
wire [(1 << (AXI_ADDR_W-12))-1:0] mon_aw_pagenum;
wire [(1 << (AXI_ADDR_W-12))-1:0] mon_ar_pagenum;

// Slave activity indicators
wire                    slv_o_busy;
wire                    slv_o_idle;
wire                    slv_o_stall;

// }}} declarations

axi4liteRandomMaster #( // {{{ mst0
  .PROB_W               (PROB_W),
  .ADDR_W               (AXI_ADDR_W),
  .DATA_BYTEW           (AXI_DATA_BYTEW),
  .ID_W                 (AXI_ID_W)
) u_mst0 (
  .i_clk                (clk),
  .i_rst                (rst),

  // Signals ordered according to the document:
  // AMBA AXI and ACE Proctocol Specification
  // ARM IHI 0022D (ID102711)
  // IDs are included for interoperability with AXI4 (B1-124).

  // Write address channel signals.
  .o_axi_AWID           (axi_awid),
  .o_axi_AWADDR         (axi_awaddr),
  .o_axi_AWPROT         (axi_awprot),
  .o_axi_AWVALID        (axi_awvalid),
  .i_axi_AWREADY        (axi_awready),

  // Write data channel signals.
  .o_axi_WDATA          (axi_wdata),
  .o_axi_WSTRB          (axi_wstrb),
  .o_axi_WVALID         (axi_wvalid),
  .i_axi_WREADY         (axi_wready),

  // Write response channel signals.
  .i_axi_BID            (axi_bid),
  .i_axi_BRESP          (axi_bresp),
  .i_axi_BVALID         (axi_bvalid),
  .o_axi_BREADY         (axi_bready),

  // Read address channel signals.
  .o_axi_ARID           (axi_arid),
  .o_axi_ARADDR         (axi_araddr),
  .o_axi_ARPROT         (axi_arprot),
  .o_axi_ARVALID        (axi_arvalid),
  .i_axi_ARREADY        (axi_arready),

  // Read data channel signals.
  .i_axi_RID            (axi_rid),
  .i_axi_RDATA          (axi_rdata),
  .i_axi_RRESP          (axi_rresp),
  .i_axi_RVALID         (axi_rvalid),
  .o_axi_RREADY         (axi_rready),

  .i_pr_aw_stall        ('d230), // 235/255 approx 90%, issue writes 1 in 10 cycles
  .i_pr_w_stall         ('d205), // 205/255 approx 80%, write data slightly faster
  .i_pr_b_stall         ('d64),
  .i_pr_ar_stall        ('d180), // 180/255 approx 70%, issue reads 3 in 10 cycles
  .i_pr_r_stall         ('d64)
); // }}} mst0

axi4liteRandomSlave #( // {{{ slv0
  .ADDR_BASE            (AXI_SLV0_ADDR_BASE),
  .N_MEM_WORD           (1*AXI_N_PAGEWORDS),
  .PROB_W               (PROB_W),
  .ADDR_W               (AXI_ADDR_W),
  .DATA_BYTEW           (AXI_DATA_BYTEW),
  .ID_W                 (AXI_ID_W)
) u_slv0 (
  .i_clk                (clk),
  .i_rst                (rst),

  // Signals ordered according to the document:
  // AMBA AXI and ACE Proctocol Specification
  // ARM IHI 0022D (ID102711)
  // IDs are included for interoperability with AXI4 (B1-124).

  // Write address channel signals.
  .i_axi_AWID           (axi_awid),
  .i_axi_AWADDR         (axi_awaddr),
  .i_axi_AWPROT         (axi_awprot),
  .i_axi_AWVALID        (axi_awvalid),
  .o_axi_AWREADY        (axi_awready),

  // Write data channel signals.
  .i_axi_WDATA          (axi_wdata),
  .i_axi_WSTRB          (axi_wstrb),
  .i_axi_WVALID         (axi_wvalid),
  .o_axi_WREADY         (axi_wready),

  // Write response channel signals.
  .o_axi_BID            (axi_bid),
  .o_axi_BRESP          (axi_bresp),
  .o_axi_BVALID         (axi_bvalid),
  .i_axi_BREADY         (axi_bready),

  // Read address channel signals.
  .i_axi_ARID           (axi_arid),
  .i_axi_ARADDR         (axi_araddr),
  .i_axi_ARPROT         (axi_arprot),
  .i_axi_ARVALID        (axi_arvalid),
  .o_axi_ARREADY        (axi_arready),

  // Read data channel signals.
  .o_axi_RID            (axi_rid),
  .o_axi_RDATA          (axi_rdata),
  .o_axi_RRESP          (axi_rresp),
  .o_axi_RVALID         (axi_rvalid),
  .i_axi_RREADY         (axi_rready),

  .i_pr_aw_stall        ('d8),
  .i_pr_w_stall         ('d16),
  .i_pr_b_stall         ('d24),
  .i_pr_ar_stall        ('d32),
  .i_pr_r_stall         ('d40),
  .i_pr_bresp_notokay   ('d48),
  .i_pr_rresp_notokay   ('d56),
  .i_pr_rddata_corrupt  ('d64),

  .o_busy               (slv_o_busy),
  .o_idle               (slv_o_idle),
  .o_stall              (slv_o_stall)
); // }}} slv0

axi4liteMonitor #( // {{{ mon0
  .ADDR_W               (AXI_ADDR_W),
  .DATA_BYTEW           (AXI_DATA_BYTEW),
  .ID_W                 (AXI_ID_W)
) u_mon0 (

  // Signals ordered according to the document:
  // AMBA AXI and ACE Proctocol Specification
  // ARM IHI 0022D (ID102711)
  // IDs are included for interoperability with AXI4 (B1-124).

  // Write address channel signals.
  .i_axi_AWID           (axi_awid),
  .i_axi_AWADDR         (axi_awaddr),
  .i_axi_AWPROT         (axi_awprot),
  .i_axi_AWVALID        (axi_awvalid),
  .i_axi_AWREADY        (axi_awready),

  // Write data channel signals.
  .i_axi_WDATA          (axi_wdata),
  .i_axi_WSTRB          (axi_wstrb),
  .i_axi_WVALID         (axi_wvalid),
  .i_axi_WREADY         (axi_wready),

  // Write response channel signals.
  .i_axi_BID            (axi_bid),
  .i_axi_BRESP          (axi_bresp),
  .i_axi_BVALID         (axi_bvalid),
  .i_axi_BREADY         (axi_bready),

  // Read address channel signals.
  .i_axi_ARID           (axi_arid),
  .i_axi_ARADDR         (axi_araddr),
  .i_axi_ARPROT         (axi_arprot),
  .i_axi_ARVALID        (axi_arvalid),
  .i_axi_ARREADY        (axi_arready),

  // Read data channel signals.
  .i_axi_RID            (axi_rid),
  .i_axi_RDATA          (axi_rdata),
  .i_axi_RRESP          (axi_rresp),
  .i_axi_RVALID         (axi_rvalid),
  .i_axi_RREADY         (axi_rready),

  .o_aw_tfr             (mon_aw_tfr),
  .o_w_tfr              (mon_w_tfr),
  .o_b_tfr              (mon_b_tfr),
  .o_ar_tfr             (mon_ar_tfr),
  .o_r_tfr              (mon_r_tfr),
  .o_b_decerr           (mon_b_decerr),
  .o_b_slverr           (mon_b_slverr),
  .o_b_okay             (mon_b_okay),
  .o_r_decerr           (mon_r_decerr),
  .o_r_slverr           (mon_r_slverr),
  .o_r_okay             (mon_r_okay),
  .o_aw_pagenum         (mon_aw_pagenum),
  .o_ar_pagenum         (mon_ar_pagenum)
);
// }}} mon0

endmodule
