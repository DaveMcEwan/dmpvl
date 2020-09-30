
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


wire          fifoUpstream_i_push;
wire          fifoUpstream_i_pop;
wire [7:0]    fifoUpstream_i_data;
wire [7:0]    fifoUpstream_o_data;
wire          fifoUpstream_o_empty;
wire          fifoUpstream_o_full;
wire          fifoUpstream_o_pushed;
wire          fifoUpstream_o_popped;
wire [2:0]    fifoUpstream_o_wrptr;
wire [2:0]    fifoUpstream_o_rdptr;
wire [7:0]    fifoUpstream_o_valid;
wire [3:0]    fifoUpstream_o_nEntries;
wire [63:0]   fifoUpstream_o_entries;

wire          fifoDnstream_i_push;
reg           fifoDnstream_i_pop;
wire [7:0]    fifoDnstream_i_data;
wire [7:0]    fifoDnstream_o_data;
wire          fifoDnstream_o_empty;
wire          fifoDnstream_o_full;
wire          fifoDnstream_o_pushed;
wire          fifoDnstream_o_popped;
wire [2:0]    fifoDnstream_o_wrptr;
wire [2:0]    fifoDnstream_o_rdptr;
wire [7:0]    fifoDnstream_o_valid;
wire [3:0]    fifoDnstream_o_nEntries;
wire [63:0]   fifoDnstream_o_entries;


assign o_bpUpstream_data = fifoUpstream_o_data;
assign o_bpUpstream_valid = !fifoUpstream_o_empty;
// NOTE: device drives i_bpUpstream_ready

// NOTE: DPI ptyBytePipe_getByte drives fifoUpstream_i_data
// NOTE: DPI ptyBytePipe_getByte drives fifoUpstream_i_push
assign fifoUpstream_i_pop = o_bpUpstream_valid && i_bpUpstream_ready;

// NOTE: device drives i_bpDnstream_data
// NOTE: device drives i_bpDnstream_valid
assign o_bpDnstream_ready = !fifoDnstream_o_full;

assign fifoDnstream_i_data = i_bpDnstream_data;
assign fifoDnstream_i_push = i_bpDnstream_valid && o_bpDnstream_ready;
// NOTE: DPI ptyBytePipe_putByte drives fifoDnstream_i_pop


fifo #(
  .WIDTH          (8),
  .DEPTH          (8),
  .FLOPS_NOT_MEM  (0)
) u_fifoUpstream ( // {{{
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (i_cg),

  .i_flush    (1'b0),
  .i_push     (fifoUpstream_i_push),
  .i_pop      (fifoUpstream_i_pop),

  .i_data     (fifoUpstream_i_data), // From PTY
  .o_data     (fifoUpstream_o_data), // To device

  .o_empty    (fifoUpstream_o_empty),
  .o_full     (fifoUpstream_o_full),

  .o_pushed   (fifoUpstream_o_pushed),
  .o_popped   (fifoUpstream_o_popped),

  .o_wrptr    (fifoUpstream_o_wrptr),
  .o_rdptr    (fifoUpstream_o_rdptr),

  .o_valid    (fifoUpstream_o_valid),
  .o_nEntries (fifoUpstream_o_nEntries),

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
  .i_push     (fifoDnstream_i_push),
  .i_pop      (fifoDnstream_i_pop),

  .i_data     (fifoDnstream_i_data), // To PTY
  .o_data     (fifoDnstream_o_data), // From device

  .o_empty    (fifoDnstream_o_empty),
  .o_full     (fifoDnstream_o_full),

  .o_pushed   (fifoDnstream_o_pushed),
  .o_popped   (fifoDnstream_o_popped),

  .o_wrptr    (fifoDnstream_o_wrptr),
  .o_rdptr    (fifoDnstream_o_rdptr),

  .o_valid    (fifoDnstream_o_valid),
  .o_nEntries (fifoDnstream_o_nEntries),

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
wire takeDataFromPty = !i_rst && i_cg && !fifoUpstream_o_full;

int getByteResult;
always @(negedge i_clk) begin
  getByteResult = -1;

  if (takeDataFromPty)
    getByteResult = ptyBytePipe_getByte(ptyMaster_fd);

  // ptyBytePipe_getByte() returns -1 if no data is available.
  fifoUpstream_i_push = getByteResult >= 0;

  fifoUpstream_i_data = getByteResult[7:0];
end


// Downstream (reply side, from BytePipe device to pty)
// Assume pty is always ready to receive into OS-level buffer.
wire giveDataToPty = !i_rst && i_cg && !fifoDnstream_o_empty;

int putByteResult;
always @(negedge i_clk) begin
  putByteResult = 0;

  if (giveDataToPty)
    putByteResult = ptyBytePipe_putByte(ptyMaster_fd, {24'd0, fifoDnstream_o_data});

  fifoDnstream_i_pop = (putByteResult != 0);
end

endmodule
