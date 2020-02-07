
`include "build/rsm_hier.v"

`define TIMEOUT_POW2 18

`ifndef MEM_N_KBYTE
  // NOTE: Changing requires changing the nwords arg to makehex.py.
  `define MEM_N_KBYTE 16
`endif

module testbench (
`ifdef VERILATOR
  /*verilator tracing_off*/
  input wire i_clk,
  input wire i_rstn,
  output reg o_dumpon
  /*verilator tracing_on*/
`endif
);

`ifndef VERILATOR
reg i_clk = 1'b0;
always #5 i_clk = ~i_clk;

reg i_rstn = 1'b0;
initial begin
  repeat (100) @(posedge i_clk);
  i_rstn <= 1'b1;
end

reg o_dumpon;
`endif

// Keep track of time to prevent runaway simulations.
reg [63:0] timetrack;
always @ (posedge i_clk)
  if (!i_rstn) timetrack <= 64'd0;
  else         timetrack <= timetrack + 1;

always @*
  if (timetrack[`TIMEOUT_POW2]) begin
    $display("TIMEOUT");
    $finish();
  end

// Veri-lator may inspect this to control VCD dumping.
// Controlled by snooping writes on AXI AW channel.
initial o_dumpon = 1'b0;

`ifndef VERILATOR
// Only produce VCD if plusarg is used to request it.
// Optional plusarg "dumplevel" may be used to control the number of hierarchy
// levels to dump, where 0 means all.
integer dumplevel;
initial begin
  if ($test$plusargs("vcd")) begin
    if (!$value$plusargs("dumplevel=%d", dumplevel)) dumplevel = 0;
    $dumpfile("build/testbench.iverilog.vcd");
    $dumpvars(dumplevel, testbench);
  end
end
`endif

// {{{ memory

wire [31:0] axi_ifu_araddr;
wire [2:0]  axi_ifu_arprot; // unused
wire        axi_ifu_arvalid;
wire        axi_ifu_arready;
reg  [31:0] axi_ifu_rdata;
wire [1:0]  axi_ifu_rresp;
reg         axi_ifu_rvalid;
wire        axi_ifu_rready;
wire [31:0] axi_lsu_awaddr;
wire [2:0]  axi_lsu_awprot; // unused
wire        axi_lsu_awvalid;
wire        axi_lsu_awready;
wire [31:0] axi_lsu_wdata;
wire [3:0]  axi_lsu_wstrb;
wire        axi_lsu_wvalid;
wire        axi_lsu_wready;
wire [1:0]  axi_lsu_bresp;
reg         axi_lsu_bvalid;
wire        axi_lsu_bready;
wire [31:0] axi_lsu_araddr;
wire [2:0]  axi_lsu_arprot; // unused
wire        axi_lsu_arvalid;
wire        axi_lsu_arready;
reg  [31:0] axi_lsu_rdata;
wire [1:0]  axi_lsu_rresp;
reg         axi_lsu_rvalid;
wire        axi_lsu_rready;

// Knowing that the UUT can only make one access from one interface at a time
// the interface can be much simplified.
wire req_valid = axi_ifu_arvalid
              || axi_lsu_awvalid
              || axi_lsu_arvalid;

reg [31:0] mem_addr;
always @*
  if      (axi_lsu_arvalid)  mem_addr = axi_lsu_araddr;
  else if (axi_lsu_awvalid)  mem_addr = axi_lsu_awaddr;
  else   /*axi_ifu_arvalid*/ mem_addr = axi_ifu_araddr;

wire mem_ready; // Memory is ready accept request.
assign axi_ifu_arready = mem_ready;
assign axi_lsu_awready = mem_ready;
assign axi_lsu_arready = mem_ready;
assign mem_ready = 1'b1;

wire [3:0]  mem_wstrb = axi_lsu_wstrb & {4{axi_lsu_awvalid}};
wire [31:0] mem_wdata = axi_lsu_wdata;

// Single-cycle reply.
wire [31:0] mem_rdata = memory[mem_addr >> 2];
always @ (posedge i_clk) begin
    axi_ifu_rvalid <= axi_ifu_arvalid;
    axi_lsu_bvalid <= axi_lsu_awvalid;
    axi_lsu_rvalid <= axi_lsu_arvalid;
    axi_ifu_rdata <= mem_rdata;
    axi_lsu_rdata <= mem_rdata;
  end

// Byte addresses 0x0000_0000 to 0x0000_ffff.
reg [31:0] memory [0:`MEM_N_KBYTE*1024/4-1] /* verilator public */;
initial $readmemh("build/sw.hex", memory);

integer memdump_fd;
integer memdump_i;
always @ (posedge i_clk)
  if (|mem_wstrb && req_valid && mem_ready) begin
    if (mem_addr < `MEM_N_KBYTE*1024) begin
      if (mem_wstrb[0]) memory[mem_addr >> 2][ 7: 0] <= mem_wdata[ 7: 0];
      if (mem_wstrb[1]) memory[mem_addr >> 2][15: 8] <= mem_wdata[15: 8];
      if (mem_wstrb[2]) memory[mem_addr >> 2][23:16] <= mem_wdata[23:16];
      if (mem_wstrb[3]) memory[mem_addr >> 2][31:24] <= mem_wdata[31:24];
    end

    else if (mem_addr == 32'h1000_0000) begin
      // print character
      $write("%c", mem_wdata[ 7: 0]);
    end

    else if (mem_addr == 32'h2000_0000) begin
      // {{{ tb control

      if (mem_wdata == 32'hacce5500) begin
        $display("PASS");
        $finish;
      end
      else if (mem_wdata == 32'hacce5501) begin
        $display("FAIL");
        $finish;
      end

      else if (mem_wdata == 32'hacce5502) begin
        $display("DUMPOFF");
        o_dumpon = 1'b0;
`ifndef VERILATOR
        $dumpoff();
`endif
      end
      else if (mem_wdata == 32'hacce5503) begin
        $display("DUMPON");
        o_dumpon = 1'b1;
`ifndef VERILATOR
        $dumpon();
`endif
      end

      else if (mem_wdata == 32'hacce5504) begin
        $display("DUMP memdump.hex");
        memdump_fd = $fopen("memdump.hex", "w");
        for (memdump_i = 0; memdump_i < `MEM_N_KBYTE*1024/4; memdump_i=memdump_i+1) begin
          $fwrite(memdump_fd, "%08x\n", memory[memdump_i]);
        end
        $fclose(memdump_fd);
      end

      else begin
        $display("UNKNOWN TB CONTROL %08x", mem_wdata);
      end

      $display("timetrack=%d", timetrack);

      // }}} tb control
    end

    else begin
      $display("OUT-OF-BOUNDS STORE TO %08x", mem_addr);
    end
  end

wire [1:0] mem_resp = (mem_addr < `MEM_N_KBYTE*1024) ? 2'b00 : 2'b11; // OKAY or DECERR
assign axi_ifu_rresp = mem_resp;
assign axi_lsu_rresp = mem_resp;
assign axi_lsu_bresp = mem_resp;

// }}} memory

rsm_m uut ( // {{{
  .i_clk(i_clk),
  .i_rstn(i_rstn),


  // Instruction AXI Read address channel signals.
  .o_axi_ifu_araddr (axi_ifu_araddr),
  .o_axi_ifu_arprot (axi_ifu_arprot),
  .o_axi_ifu_arvalid(axi_ifu_arvalid),
  .i_axi_ifu_arready(axi_ifu_arready),

  // Instruction AXI Read data channel signals.
  .i_axi_ifu_rdata  (axi_ifu_rdata),
  .i_axi_ifu_rresp  (axi_ifu_rresp),
  .i_axi_ifu_rvalid (axi_ifu_rvalid),
  .o_axi_ifu_rready (axi_ifu_rready),


  // Data AXI Write address channel signals.
  .o_axi_lsu_awaddr (axi_lsu_awaddr),
  .o_axi_lsu_awprot (axi_lsu_awprot),
  .o_axi_lsu_awvalid(axi_lsu_awvalid),
  .i_axi_lsu_awready(axi_lsu_awready),

  // Data AXI Write data channel signals.
  .o_axi_lsu_wdata  (axi_lsu_wdata),
  .o_axi_lsu_wstrb  (axi_lsu_wstrb),
  .o_axi_lsu_wvalid (axi_lsu_wvalid),
  .i_axi_lsu_wready (axi_lsu_wready),

  // Data AXI Write response channel signals.
  .i_axi_lsu_bresp  (axi_lsu_bresp),
  .i_axi_lsu_bvalid (axi_lsu_bvalid),
  .o_axi_lsu_bready (axi_lsu_bready),

  // Data AXI Read address channel signals.
  .o_axi_lsu_araddr (axi_lsu_araddr),
  .o_axi_lsu_arprot (axi_lsu_arprot),
  .o_axi_lsu_arvalid(axi_lsu_arvalid),
  .i_axi_lsu_arready(axi_lsu_arready),

  // Data AXI Read data channel signals.
  .i_axi_lsu_rdata  (axi_lsu_rdata),
  .i_axi_lsu_rresp  (axi_lsu_rresp),
  .i_axi_lsu_rvalid (axi_lsu_rvalid),
  .o_axi_lsu_rready (axi_lsu_rready)
); // }}}
endmodule
