
module ptyBytePipe #(
  parameter NUMBER = 0 // in {0..4}
) (
  input  wire           i_clk,
  input  wire           i_rst,
  input  wire           i_cg,

  // verboseOn has precedence over verboseOff
  input wire            i_verboseOn,
  input wire            i_verboseOff,

  output wire [7:0]     o_bpUpstream_data,
  output wire           o_bpUpstream_valid,
  input  wire           i_bpUpstream_ready,

  input  wire [7:0]     i_bpDnstream_data,
  input  wire           i_bpDnstream_valid,
  output wire           o_bpDnstream_ready
);

import "DPI-C" function void ptyBytePipe_verboseOn();
import "DPI-C" function void ptyBytePipe_verboseOff();
import "DPI-C" function int ptyBytePipe_init(string ptsSymlinkPath);
import "DPI-C" function int ptyBytePipe_getByte(int fd);
import "DPI-C" function int ptyBytePipe_putByte(int fd, int b);


wire [7:0]    fifoUpstream_i_data;
wire          fifoUpstream_i_valid; // push
wire          fifoUpstream_o_ready; // !full
wire [7:0]    fifoUpstream_o_data;
wire          fifoUpstream_o_valid; // !empty
wire          fifoUpstream_i_ready; // pop
wire          fifoUpstream_o_pushed;
wire          fifoUpstream_o_popped;
wire [2:0]    fifoUpstream_o_wrptr;
wire [2:0]    fifoUpstream_o_rdptr;
wire [7:0]    fifoUpstream_o_validEntries;
wire [3:0]    fifoUpstream_o_nEntries;
wire [63:0]   fifoUpstream_o_entries;

wire [7:0]    fifoDnstream_i_data;
wire          fifoDnstream_i_valid; // push
wire          fifoDnstream_o_ready; // !full
wire [7:0]    fifoDnstream_o_data;
wire          fifoDnstream_o_valid; // !empty
reg           fifoDnstream_i_ready; // pop
wire          fifoDnstream_o_pushed;
wire          fifoDnstream_o_popped;
wire [2:0]    fifoDnstream_o_wrptr;
wire [2:0]    fifoDnstream_o_rdptr;
wire [7:0]    fifoDnstream_o_validEntries;
wire [3:0]    fifoDnstream_o_nEntries;
wire [63:0]   fifoDnstream_o_entries;


assign o_bpUpstream_data = fifoUpstream_o_data;
assign o_bpUpstream_valid = fifoUpstream_o_valid;
// NOTE: device drives i_bpUpstream_ready

// NOTE: DPI ptyBytePipe_getByte drives fifoUpstream_i_data
// NOTE: DPI ptyBytePipe_getByte drives fifoUpstream_i_valid
assign fifoUpstream_i_ready = o_bpUpstream_valid && i_bpUpstream_ready;

// NOTE: device drives i_bpDnstream_data
// NOTE: device drives i_bpDnstream_valid
assign o_bpDnstream_ready = fifoDnstream_o_ready;

assign fifoDnstream_i_data = i_bpDnstream_data;
assign fifoDnstream_i_valid = i_bpDnstream_valid && o_bpDnstream_ready;
// NOTE: DPI ptyBytePipe_putByte drives fifoDnstream_i_ready


fifo #(
  .WIDTH          (8),
  .DEPTH          (8),
  .FLOPS_NOT_MEM  (0)
) u_fifoUpstream ( // {{{
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (i_cg),

  .i_flush    (1'b0),

  .i_data     (fifoUpstream_i_data), // From PTY
  .i_valid    (fifoUpstream_i_valid),
  .o_ready    (fifoUpstream_o_ready),

  .o_data     (fifoUpstream_o_data), // To device
  .o_valid    (fifoUpstream_o_valid),
  .i_ready    (fifoUpstream_i_ready),

  .o_pushed   (fifoUpstream_o_pushed),
  .o_popped   (fifoUpstream_o_popped),

  .o_wrptr    (fifoUpstream_o_wrptr),
  .o_rdptr    (fifoUpstream_o_rdptr),

  .o_validEntries (fifoUpstream_o_validEntries),
  .o_nEntries     (fifoUpstream_o_nEntries),

  .o_entries  (fifoUpstream_o_entries)
); // }}}

fifo #(
  .WIDTH          (8),
  .DEPTH          (8),
  .FLOPS_NOT_MEM  (0)
) u_fifoDnstream ( // {{{
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (i_cg),

  .i_flush    (1'b0),

  .i_data     (fifoDnstream_i_data), // To PTY
  .i_valid    (fifoDnstream_i_valid),
  .o_ready    (fifoDnstream_o_ready),

  .o_data     (fifoDnstream_o_data), // From device
  .o_valid    (fifoDnstream_o_valid),
  .i_ready    (fifoDnstream_i_ready),

  .o_pushed   (fifoDnstream_o_pushed),
  .o_popped   (fifoDnstream_o_popped),

  .o_wrptr    (fifoDnstream_o_wrptr),
  .o_rdptr    (fifoDnstream_o_rdptr),

  .o_validEntries (fifoDnstream_o_validEntries),
  .o_nEntries     (fifoDnstream_o_nEntries),

  .o_entries  (fifoDnstream_o_entries)
); // }}}


int ptyMaster_fd;
initial begin
  ptyBytePipe_verboseOn();

  case (NUMBER)
    0: ptyMaster_fd = ptyBytePipe_init("./ptyBytePipe_bp0");
    1: ptyMaster_fd = ptyBytePipe_init("./ptyBytePipe_bp1");
    2: ptyMaster_fd = ptyBytePipe_init("./ptyBytePipe_bp2");
    3: ptyMaster_fd = ptyBytePipe_init("./ptyBytePipe_bp3");
    4: ptyMaster_fd = ptyBytePipe_init("./ptyBytePipe_bp4");
    default: begin
      $display("Unsupported ptyBytePipe NUMBER parameter.");
      $finish;
    end
  endcase
end


always @(posedge i_clk) begin
  if (i_verboseOff)   ptyBytePipe_verboseOff();
  if (i_verboseOn)    ptyBytePipe_verboseOn();
end


// Upstream (request side, from pty to BytePipe device)
// Only bother checking whether the pty has data when fifo has space.
wire takeDataFromPty = !i_rst && i_cg && fifoUpstream_o_ready;

int getByteResult;
always @(negedge i_clk) begin
  getByteResult = -1;

  if (takeDataFromPty)
    getByteResult = ptyBytePipe_getByte(ptyMaster_fd);

  // ptyBytePipe_getByte() returns -1 if no data is available.
  fifoUpstream_i_valid = getByteResult >= 0;

  fifoUpstream_i_data = getByteResult[7:0];
end


// Downstream (reply side, from BytePipe device to pty)
// Assume pty is always ready to receive into OS-level buffer.
wire giveDataToPty = !i_rst && i_cg && fifoDnstream_o_valid;

int putByteResult;
always @(negedge i_clk) begin
  putByteResult = 0;

  if (giveDataToPty)
    putByteResult = ptyBytePipe_putByte(ptyMaster_fd, {24'd0, fifoDnstream_o_data});

  fifoDnstream_i_ready = (putByteResult != 0);
end

endmodule
