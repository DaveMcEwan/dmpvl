/** correlator_tb.v - Testbench for fifo
 * Expose BytePipe as a PTY for external script to use.
 */
module correlator_tb (

  output reg            common_x,
  output reg            common_y,

  output reg            common_cg,

  input  wire           i_clk,
  input  wire           i_rst

);

import "DPI-C" function int ptyBytePipe_init(string ptsSymlinkPath);
import "DPI-C" function int ptyBytePipe_putByte(int fd, int b);
import "DPI-C" function int ptyBytePipe_getByte(int fd);

int bp0_fd; // Master file descriptor for pty
int bp0_upstream_fromPty;
initial begin
  bp0_fd = ptyBytePipe_init("./ptyBytePipe_bp0");
  bp0_upstream_fromPty = 0;
end

// Upstream (request side, from pty to BytePipe device)
reg  [7:0]  bp0_upstream_data;
reg         bp0_upstream_valid;
wire        bp0_upstream_ready;
always @(posedge i_clk) begin
  if (!i_rst && common_cg) begin
    bp0_upstream_fromPty = 0;

    // Only bother checking whether the pty has data when device is ready to
    // receive it.
    if (bp0_upstream_ready)
      bp0_upstream_fromPty = ptyBytePipe_getByte(bp0_fd);
  end

  // ptyBytePipe_getByte() should return -1 if no data is available.
  bp0_upstream_valid = bp0_upstream_fromPty >= 0;

  bp0_upstream_data = bp0_upstream_fromPty[7:0];
end

// Downstream (reply side, from BytePipe device to pty)
// Assume pty is always ready to receive into OS-level buffer.
wire [7:0]  bp0_dnstream_data;
wire        bp0_dnstream_valid;
wire        bp0_dnstream_ready = 1'b1;
always @(posedge i_clk) if (!i_rst && common_cg) begin
  if (bp0_dnstream_valid && bp0_dnstream_ready)
    ptyBytePipe_putByte(bp0_fd, {24'd0, bp0_dnstream_data});
end

// TODO: These should be the only two lines which setup bp0.
//`include "ptyBytePipe.vh" TODO
//`ptyBytePipe_bp0(i_clk, common_cg, i_rst) TODO

always @(posedge i_clk) begin
  common_cg     <= ($random % 100) != 0; // Drop i_cg 1/100.
  common_x      <= ($random % 5) == 0; // Pulse i_push high 1/5.
  common_y      <= ($random % 6) == 0; // Pulse i_pop high 1/6.
end

correlator u_correlator (
  .i_clk      (i_clk),
  .i_rst      (i_rst),
  .i_cg       (common_cg),

  .i_x        (common_x),
  .i_y        (common_y),

  .i_bp_data  (bp0_upstream_data),
  .i_bp_valid (bp0_upstream_valid),
  .o_bp_ready (bp0_upstream_ready),

  .o_bp_data  (bp0_dnstream_data),
  .o_bp_valid (bp0_dnstream_valid),
  .i_bp_ready (bp0_dnstream_ready)
);

endmodule
