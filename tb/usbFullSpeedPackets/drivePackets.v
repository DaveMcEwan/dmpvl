`include "dff.vh"

// Drive random packets to usbFullSpeedPacketSender.
// No attempt made at packet level protocol compliance as this is just to
// stress the packet encode/decode logic.
module drivePackets #(
  parameter AS_HOST_NOT_DEV = 1, // 1=Operate as host, 0=Operate as device/function.
  parameter MAX_PKT = 8  // in {8,16,32,64}. wMaxPacketSize
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  input  wire                       i_ready,
  output wire                       o_valid,

  output wire [3:0]                 o_pid,
  output wire [8*MAX_PKT-1:0]       o_data,
  output wire [$clog2(MAX_PKT):0]   o_data_nBytes
);

`include "usbSpec.vh"

// Randomly drop o_valid for 7/8 of cycles.
reg [2:0] rnd_valid;
`ifndef VERILATOR
always @(posedge i_clk)
  rnd_valid = $urandom_range(7, 0);
`endif
assign o_valid = (rnd_valid == 3'b0);

wire [3:0] validPids [9];
assign validPids[8] = PID_HANDSHAKE_STALL;
assign validPids[7] = PID_HANDSHAKE_NAK;
// below: host+dev, above: dev-only
assign validPids[6] = PID_HANDSHAKE_ACK;
assign validPids[5] = PID_DATA_DATA1;
assign validPids[4] = PID_DATA_DATA0;
// below: host-only, above: host+dev
assign validPids[3] = PID_TOKEN_SETUP;
assign validPids[2] = PID_TOKEN_SOF;
assign validPids[1] = PID_TOKEN_IN;
assign validPids[0] = PID_TOKEN_OUT;

reg [3:0]                 pidIdx;
reg [3:0]                 pid;
reg [8*MAX_PKT-1:0]       data;
reg [$clog2(MAX_PKT):0]   data_nBytes;

`ifndef VERILATOR
always @(posedge i_clk or negedge i_rst)
  if (!i_rst || (o_valid && i_ready)) begin

    if (AS_HOST_NOT_DEV)
      pidIdx = $urandom_range(6, 0);
    else
      pidIdx = $urandom_range(8, 4);

    pid = validPids[pidIdx];
    data = {$urandom(), $urandom()};
    data_nBytes = (pidIdx < 4) ? 2 : $urandom_range(MAX_PKT, 1);
  end
`endif

assign o_pid = pid;
assign o_data = data;
assign o_data_nBytes = data_nBytes;

endmodule
