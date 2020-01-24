// Monitor for one AXI port.
module axi4liteMonitor #(
  parameter ADDR_W = 16,
  parameter DATA_BYTEW = 4,
  parameter ID_W = 4
) (
  // Signals ordered according to the document:
  // AMBA AXI and ACE Proctocol Specification
  // ARM IHI 0022D (ID102711)
  // IDs are included for interoperability with AXI4 (B1-124).

  // Write address channel signals.
  input  wire [ID_W-1:0]                i_axi_AWID,
  input  wire [ADDR_W-1:0]              i_axi_AWADDR,
  input  wire [2:0]                     i_axi_AWPROT,
  input  wire                           i_axi_AWVALID,
  input  wire                           i_axi_AWREADY,

  // Write data channel signals.
  input  wire [(DATA_BYTEW*8)-1:0]      i_axi_WDATA,
  input  wire [3:0]                     i_axi_WSTRB,
  input  wire                           i_axi_WVALID,
  input  wire                           i_axi_WREADY,

  // Write response channel signals.
  input  wire [ID_W-1:0]                i_axi_BID,
  input  wire [1:0]                     i_axi_BRESP,
  input  wire                           i_axi_BVALID,
  input  wire                           i_axi_BREADY,

  // Read address channel signals.
  input  wire [ID_W-1:0]                i_axi_ARID,
  input  wire [ADDR_W-1:0]              i_axi_ARADDR,
  input  wire [2:0]                     i_axi_ARPROT,
  input  wire                           i_axi_ARVALID,
  input  wire                           i_axi_ARREADY,

  // Read data channel signals.
  input  wire [ID_W-1:0]                i_axi_RID,
  input  wire [(DATA_BYTEW*8)-1:0]      i_axi_RDATA,
  input  wire [1:0]                     i_axi_RRESP,
  input  wire                           i_axi_RVALID,
  input  wire                           i_axi_RREADY,


  output wire                           o_aw_tfr,
  output wire                           o_w_tfr,
  output wire                           o_b_tfr,
  output wire                           o_ar_tfr,
  output wire                           o_r_tfr,
  output wire                           o_b_decerr,
  output wire                           o_b_slverr,
  output wire                           o_b_okay,
  output wire                           o_r_decerr,
  output wire                           o_r_slverr,
  output wire                           o_r_okay,
  output wire [(1 << (ADDR_W-12))-1:0]  o_aw_pagenum,
  output wire [(1 << (ADDR_W-12))-1:0]  o_ar_pagenum
);

`include "ambaSpec.vh"

localparam OFFSET_W = 10;
localparam OFFSET_L = 2;
localparam OFFSET_H = OFFSET_W + OFFSET_L - 1; // 11
localparam PAGENUM_L = OFFSET_H + 1;
localparam PAGENUM_H = ADDR_W - 1;
localparam PAGENUM_W = PAGENUM_H - PAGENUM_L + 1;
localparam N_PAGE = 1 << PAGENUM_W;

assign o_aw_tfr = i_axi_AWVALID && i_axi_AWREADY;
assign o_w_tfr  = i_axi_WVALID  && i_axi_WREADY;
assign o_b_tfr  = i_axi_BVALID  && i_axi_AWREADY;
assign o_ar_tfr = i_axi_ARVALID && i_axi_ARREADY;
assign o_r_tfr  = i_axi_RVALID  && i_axi_RREADY;

assign o_b_decerr = o_b_tfr && (i_axi_BRESP == AXI_RESP_DECERR);
assign o_b_slverr = o_b_tfr && (i_axi_BRESP == AXI_RESP_SLVERR);
assign o_b_okay   = o_b_tfr && (i_axi_BRESP == AXI_RESP_OKAY);
assign o_r_decerr = o_r_tfr && (i_axi_RRESP == AXI_RESP_DECERR);
assign o_r_slverr = o_r_tfr && (i_axi_RRESP == AXI_RESP_SLVERR);
assign o_r_okay   = o_r_tfr && (i_axi_RRESP == AXI_RESP_OKAY);

genvar i;
generate for (i=0; i < N_PAGE; i=i+1) begin : pagenum_b
  assign o_aw_pagenum[i] =
    o_aw_tfr &&
    (i_axi_AWADDR[PAGENUM_H:PAGENUM_L] == i);

  assign o_ar_pagenum[i] =
    o_ar_tfr &&
    (i_axi_ARADDR[PAGENUM_H:PAGENUM_L] == i);
end : pagenum_b endgenerate

endmodule
