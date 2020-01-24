`include "dff.vh"
`include "asrt.vh"

module driveEndpointTx #(
  parameter MAX_PKT = 8
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  output wire                       o_etStall,

  input  wire                       i_etReady,
  output wire                       o_etValid,
  output wire [8*MAX_PKT-1:0]       o_etData,
  output wire [$clog2(MAX_PKT):0]   o_etData_nBytes,

  input  wire [2:0]                 i_txnType // {SETUP, OUT, IN}
);

`include "usbSpec.vh"

wire accepted = i_etReady && o_etValid;

`asrt(txnType, i_clk, !i_rst && accepted, $onehot(i_txnType))

reg [8*MAX_PKT-1:0]       data;
reg [$clog2(MAX_PKT):0]   data_nBytes;

`dff_nocg_srst(reg [8*MAX_PKT-1:0], data, i_clk, i_rst, '0)
`dff_nocg_srst(reg [$clog2(MAX_PKT):0], data_nBytes, i_clk, i_rst, '0)
`ifndef VERILATOR
initial begin
  data_q = '0;
  data_nBytes_q = 'd8;
end
always @* data_d = accepted ? {$urandom(), $urandom()} : data_q;
always @* data_nBytes_d = accepted ? (i_txnType[2] ? 'd8 : $urandom_range(MAX_PKT, 0)) : data_nBytes_q;
`endif

assign o_etData = data_q;
assign o_etData_nBytes = data_nBytes_q;

/*
// Randomly drop o_etValid for 1/8 of cycles.
reg [2:0] rnd_valid;
`ifndef VERILATOR
always @(posedge i_clk)
  rnd_valid = $urandom_range(7, 0);
`endif
assign o_etValid = (rnd_valid != 3'b0);
*/
assign o_etValid = 1'b1;


wire stalled = o_etStall && accepted;

// Randomly drop o_etStall for 7/8 of cycles.
reg [2:0] rnd_stall;
`ifndef VERILATOR
always @(posedge i_clk)
  rnd_stall = $urandom_range(7, 0);
`endif
assign o_etStall = (rnd_stall == 3'b0);


// https://en.wikipedia.org/wiki/USB_(Communications)#Setup_packet
wire [ 4:0] bmRequestTypeRecipient  = data_q[4:0];
wire [ 1:0] bmRequestTypeType       = data_q[6:5];
wire        bmRequestTypeDirection  = data_q[7];
wire [ 7:0] bRequest                = data_q[15:8];
wire [15:0] wValue                  = data_q[31:16];
wire [15:0] wIndex                  = data_q[47:32];
wire [15:0] wLength                 = data_q[63:48];

always @(posedge i_clk) if (accepted) begin : info
  string s_txnType;
  string s_data;
  string s_stalled;

  if (i_txnType[2])
    $sformat(s_txnType, "Endpoint[SETUP]");
  else if (i_txnType[1])
    $sformat(s_txnType, "Endpoint[OUT]");
  else if (i_txnType[0])
    $sformat(s_txnType, "Endpoint[IN]");
  else
    $sformat(s_txnType, "Endpoint[UNKNOWN]");

  $sformat(s_data, "data=0x%0h, nBytes=%0d", data_q, o_etData_nBytes);

  if (stalled)
    $sformat(s_stalled, "STALLED");
  else
    $sformat(s_stalled, "");

  $display("INFO:t%0t:%m: %s sent %s.", $time, s_txnType, s_data, s_stalled);

  // https://en.wikipedia.org/wiki/USB_(Communications)#Setup_packet
  if (i_txnType[2]) begin
    string s_bmRequestTypeRecipient;
    string s_bmRequestTypeType;
    string s_bmRequestTypeDirection;
    string s_bRequest;
    string s_wValue;
    string s_wIndex;
    string s_wLength;

    case (bmRequestTypeRecipient)
      5'd0: $sformat(s_bmRequestTypeRecipient, "Device");
      5'd1: $sformat(s_bmRequestTypeRecipient, "Interface");
      5'd2: $sformat(s_bmRequestTypeRecipient, "Endpoint");
      5'd3: $sformat(s_bmRequestTypeRecipient, "Other");
      default: $sformat(s_bmRequestTypeRecipient, "UNKNOWN");
    endcase

    case (bmRequestTypeType)
      2'd0: $sformat(s_bmRequestTypeType, "Standard");
      2'd1: $sformat(s_bmRequestTypeType, "Class");
      2'd2: $sformat(s_bmRequestTypeType, "Vendor");
      default: $sformat(s_bmRequestTypeType, "UNKNOWN");
    endcase

    if (bmRequestTypeDirection == 1'b0)
      $sformat(s_bmRequestTypeDirection, "Host-to-device");
    else
      $sformat(s_bmRequestTypeDirection, "Device-to-host");

    case (bRequest)
      BREQUEST_GET_STATUS:        $sformat(s_bRequest, "GET_STATUS");
      BREQUEST_CLEAR_FEATURE:     $sformat(s_bRequest, "CLEAR_FEATURE");
      BREQUEST_SET_STATUS:        $sformat(s_bRequest, "SET_STATUS");
      BREQUEST_SET_ADDRESS:       $sformat(s_bRequest, "SET_ADDRESS");
      BREQUEST_GET_DESCRIPTOR:    $sformat(s_bRequest, "GET_DESCRIPTOR");
      BREQUEST_SET_DESCRIPTOR:    $sformat(s_bRequest, "SET_DESCRIPTOR");
      BREQUEST_GET_CONFIGURATION: $sformat(s_bRequest, "GET_CONFIGURATION");
      BREQUEST_SET_CONFIGURATION: $sformat(s_bRequest, "SET_CONFIGURATION");
      BREQUEST_GET_INTERFACE:     $sformat(s_bRequest, "GET_INTERFACE");
      BREQUEST_SET_INTERFACE:     $sformat(s_bRequest, "SET_INTERFACE");
      BREQUEST_SYNCH_FRAME:       $sformat(s_bRequest, "SYNCH_FRAME");
      default: $sformat(s_bRequest, "UNKNOWN");
    endcase

    $display("  :bmRequestType.Recipient=%0d=%s", bmRequestTypeRecipient, s_bmRequestTypeRecipient);
    $display("  :bmRequestType.Type=%d=%s", bmRequestTypeType, s_bmRequestTypeType);
    $display("  :bmRequestType.Direction=%d=%s", bmRequestTypeDirection, s_bmRequestTypeDirection);
    $display("  :bRequest=%0d=%s", bRequest, s_bRequest);
    $display("  :wValue=%0h", wValue);
    $display("  :wIndex=%0h", wIndex);
    $display("  :wLength=%0h", wLength);
  end

end : info

endmodule
