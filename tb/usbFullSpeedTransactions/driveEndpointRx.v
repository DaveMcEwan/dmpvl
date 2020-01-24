`include "dff.vh"
`include "asrt.vh"

module driveEndpointRx #(
  parameter MAX_PKT = 8
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  output wire                       o_erStall,

  output wire                       o_erReady,
  input  wire                       i_erValid,
  input  wire [8*MAX_PKT-1:0]       i_erData,
  input  wire [$clog2(MAX_PKT):0]   i_erData_nBytes,

  input  wire [2:0]                 i_txnType // {SETUP, OUT, IN}
);

`include "usbSpec.vh"

wire accepted = o_erReady && i_erValid;

`asrt(txnType, i_clk, !i_rst && accepted, $onehot(i_txnType))


// Randomly drop o_erReady for 1/8 of cycles.
// Except for SETUP transactions which must always accept DATA0.
reg [2:0] rnd_ready;
`ifndef VERILATOR
always @(posedge i_clk)
  rnd_ready = $urandom_range(7, 0);
`endif
assign o_erReady = i_txnType[2] || (rnd_ready != 3'b0);


wire stalled = o_erStall && accepted;

// Randomly drop o_erStall for 7/8 of cycles.
reg [2:0] rnd_stall;
`ifndef VERILATOR
always @(posedge i_clk)
  rnd_stall = $urandom_range(7, 0);
`endif
assign o_erStall = (rnd_stall == 3'b0);


// https://en.wikipedia.org/wiki/USB_(Communications)#Setup_packet
wire [ 4:0] bmRequestTypeRecipient  = i_erData[4:0];
wire [ 1:0] bmRequestTypeType       = i_erData[6:5];
wire        bmRequestTypeDirection  = i_erData[7];
wire [ 7:0] bRequest                = i_erData[15:8];
wire [15:0] wValue                  = i_erData[31:16];
wire [15:0] wIndex                  = i_erData[47:32];
wire [15:0] wLength                 = i_erData[63:48];

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

  $sformat(s_data, "data=0x%0h, nBytes=%0d", i_erData, i_erData_nBytes);

  if (stalled)
    $sformat(s_stalled, "STALLED");
  else
    $sformat(s_stalled, "");

  $display("INFO:t%0t:%m: %s received %s.", $time, s_txnType, s_data);

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
