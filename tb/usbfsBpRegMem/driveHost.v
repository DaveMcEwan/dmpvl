`include "dff.vh"

// Drive control transfers, then random data to/from usbFullSpeedSerial.
// The configuration (control transfers) stage is a very directed test.
module driveHost (
  input  wire                       i_clk,
  input  wire                       i_rst,

  // Control IN
  output wire                       o_er0Ready, // TODO
  input  wire                       i_er0Valid,
  input  wire [8*MAX_PKT-1:0]       i_er0Data,
  input  wire [$clog2(MAX_PKT):0]   i_er0Data_nBytes,

  // Control OUT
  input  wire                       i_et0Ready,
  output wire                       o_et0Valid, // TODO
  output reg  [8*MAX_PKT-1:0]       o_et0Data,
  output reg  [$clog2(MAX_PKT):0]   o_et0Data_nBytes,

  // Data IN
  output wire                       o_er1Ready, // TODO
  input  wire                       i_er1Valid,
  input  wire [8*MAX_PKT-1:0]       i_er1Data,
  input  wire [$clog2(MAX_PKT):0]   i_er1Data_nBytes,

  // Data OUT
  input  wire                       i_et1Ready,
  output wire                       o_et1Valid, // TODO
  output reg  [8*MAX_PKT-1:0]       o_et1Data,
  output reg  [$clog2(MAX_PKT):0]   o_et1Data_nBytes,

  input  wire                       i_txnReady,
  output wire                       o_txnValid,
  output reg  [2:0]                 o_txnType,
  output reg  [6:0]                 o_txnAddr,
  output reg  [3:0]                 o_txnEndp,

  // Flags from host transactor.
  input  wire [2:0]                 i_txnType
);

localparam MAX_PKT = 8;

`include "usbSpec.vh"

wire txn_accepted = i_txnReady && o_txnValid;
`dff_nocg_srst(reg [31:0], nTxns, i_clk, i_rst, '0)
always @*
  if (txn_accepted) begin
    nTxns_d = nTxns_q + 1;
    $display("INFO:t%0t:%m: nTxns=%0d", $time, nTxns_q);
  end
  else
    nTxns_d = nTxns_q;

// Randomly drop o_txnValid for 7/8 of cycles.
reg [2:0] rnd_valid;
`ifndef VERILATOR
always @(posedge i_clk)
  rnd_valid = $urandom_range(7, 0);
`endif
assign o_txnValid = !i_rst && (rnd_valid == 3'b0);


localparam DEVADDR = 7'd55; // 7'h37

wire [63:0] setupPayload_setAddress = {
  16'd0,    // wLength, no data stage
  16'd0,    // wIndex
  9'd0, 7'(DEVADDR), // wValue
  8'd5,     // bRequest SET_ADDRESS
  1'd0,     // bmRequestType Direction=Host-to-device
  2'd0,     // bmRequestType Type=Standard
  5'd0      // bmRequestType Recipient=Device
};

wire [63:0] setupPayload_getDescriptor_device = {
  16'd18,   // wLength, exact length
  //16'd64,   // wLength, Linux behaviour
  16'd0,    // wIndex
  BDESCRIPTORTYPE_DEVICE, 8'd0, // wValue
  8'd6,     // bRequest GET_DESCRIPTOR
  1'd1,     // bmRequestType Direction=Device-to-host
  2'd0,     // bmRequestType Type=Standard
  5'd0      // bmRequestType Recipient=Device
};

wire [63:0] setupPayload_getDescriptor_config = {
  16'hffff, // wLength, max length
  16'd0,    // wIndex
  BDESCRIPTORTYPE_CONFIGURATION, 8'd0, // wValue
  8'd6,     // bRequest GET_DESCRIPTOR
  1'd1,     // bmRequestType Direction=Device-to-host
  2'd0,     // bmRequestType Type=Standard
  5'd0      // bmRequestType Recipient=Device
};

wire [63:0] setupPayload_getDescriptor_string = { // unsupported, requestError
  16'hffff, // wLength, max length
  16'd0,    // wIndex
  BDESCRIPTORTYPE_STRING, 8'd0, // wValue
  8'd6,     // bRequest GET_DESCRIPTOR
  1'd1,     // bmRequestType Direction=Device-to-host
  2'd0,     // bmRequestType Type=Standard
  5'd0      // bmRequestType Recipient=Device
};

// {SETUP, OUT, IN}
// Do SETUPs before any OUTs or INs.
localparam TXNTYPE_SETUP = 3'b100;
localparam TXNTYPE_OUT = 3'b010;
localparam TXNTYPE_IN = 3'b001;

always @*
  case (nTxns_q)
    // {{{ GET_DESCRIPTOR DEVICE
    'd0: begin
      o_txnType = TXNTYPE_SETUP;
      o_txnAddr = 7'd0; // Default address
      o_txnEndp = 4'd0; // Control endpoint
      o_et0Data = setupPayload_getDescriptor_device;
      o_et0Data_nBytes = 'd8;
    end
    'd1: begin
      o_txnType = TXNTYPE_IN;
    end
    'd2: begin
      o_txnType = TXNTYPE_IN;
    end
    'd3: begin
      o_txnType = TXNTYPE_IN;
    end
    'd4: begin
      o_txnType = TXNTYPE_OUT;
      o_et0Data_nBytes = 'd0;
    end
    // }}} GET_DESCRIPTOR DEVICE

    // {{{ GET_DESCRIPTOR CONFIG
    // Config descriptor for /dev/ttyUSB* is 32B
    // Config descriptor for /dev/ttyACM* is 67B
    'd5: begin
      o_txnType = TXNTYPE_SETUP;
      o_et0Data = setupPayload_getDescriptor_config;
      o_et0Data_nBytes = 'd8;
    end
    'd6: begin
      o_txnType = TXNTYPE_IN;
    end
    'd7: begin
      o_txnType = TXNTYPE_IN;
    end
    'd8: begin
      o_txnType = TXNTYPE_IN;
    end
    'd9: begin
      o_txnType = TXNTYPE_IN;
    end
    'd10: begin
      o_txnType = TXNTYPE_IN; // Should NAK on extra IN transactions.
    end
    'd11: begin
      o_txnType = TXNTYPE_IN;
    end
    'd12: begin
      o_txnType = TXNTYPE_IN;
    end
    'd13: begin
      o_txnType = TXNTYPE_IN;
    end
    'd14: begin
      o_txnType = TXNTYPE_IN;
    end
    'd15: begin
      o_txnType = TXNTYPE_OUT;
      o_et0Data_nBytes = 'd0;
    end
    // }}} GET_DESCRIPTOR CONFIG

    // {{{ GET_DESCRIPTOR STRING
    'd16: begin
      o_txnType = TXNTYPE_SETUP;
      o_et0Data = setupPayload_getDescriptor_string;
      o_et0Data_nBytes = 'd8;
    end
    'd17: begin // Should STALL for unsupported descriptor.
      o_txnType = TXNTYPE_IN;
    end
    // }}} GET_DESCRIPTOR STRING

    // {{{ SET_ADDRESS
    'd18: begin
      o_txnType = TXNTYPE_SETUP;
      o_et0Data = setupPayload_setAddress;
      o_et0Data_nBytes = 'd8;
    end
    'd19: begin // Should keep default address until this completes.
      o_txnType = TXNTYPE_IN;
    end
    // }}} SET_ADDRESS

    // {{{ GET_DESCRIPTOR STRING (to new device address)
    'd20: begin
      o_txnType = TXNTYPE_SETUP;
      o_txnAddr = DEVADDR; // New address
      o_et0Data = setupPayload_getDescriptor_string;
      o_et0Data_nBytes = 'd8;
    end
    'd21: begin // Should STALL for unsupported descriptor.
      o_txnType = TXNTYPE_IN;
    end
    // }}} GET_DESCRIPTOR STRING (to new device address)

    // {{{ BytePipe transactions
    'd22: begin
      o_txnType = TXNTYPE_OUT;
      o_txnEndp = 4'd1; // Data endpoint
      o_et1Data = 64'h0780; // Burst of length 7.
      o_et1Data_nBytes = 'd2;
    end
    'd23: begin // Expect to see 'h00 as value @0.
      o_txnType = TXNTYPE_IN;
    end
    'd24: begin
      o_txnType = TXNTYPE_OUT;
      o_et1Data = 64'h45; // Read (burst) @0x45
      o_et1Data_nBytes = 'd1;
    end
    'd25: begin // Expect to see 8B returned.
      o_txnType = TXNTYPE_IN;
    end
    'd26: begin
      o_txnType = TXNTYPE_OUT;
      o_et1Data = 64'h46; // Read (single) @0x46
      o_et1Data_nBytes = 'd1;
    end
    'd27: begin // Expect to see 1B returned.
      o_txnType = TXNTYPE_IN;
    end
    // }}} BytePipe transactions

    // Random OUT/IN transfers, mostly to the correct device on endpoint 1.
    default: begin
`ifndef VERILATOR
      o_txnType = 1 << $urandom_range(1, 0);
      o_txnAddr = ($urandom_range(10, 0) == 0) ? $urandom_range(127, 0) : DEVADDR;
      o_txnEndp = ($urandom_range(10, 0) == 0) ? 0 : 1;
`endif
    end
  endcase

wire [ 4:0] bmRequestTypeRecipient  = o_et0Data[4:0];
wire [ 1:0] bmRequestTypeType       = o_et0Data[6:5];
wire        bmRequestTypeDirection  = o_et0Data[7];
wire [ 7:0] bRequest                = o_et0Data[15:8];
wire [15:0] wValue                  = o_et0Data[31:16];
wire [15:0] wIndex                  = o_et0Data[47:32];
wire [15:0] wLength                 = o_et0Data[63:48];
always @(posedge i_clk) if (txn_accepted) begin : info
  string s_txnType;
  string s_data;

  if (o_txnType[2])
    $sformat(s_txnType, "Endpoint[SETUP]");
  else if (o_txnType[1])
    $sformat(s_txnType, "Endpoint[OUT]");
  else if (o_txnType[0])
    $sformat(s_txnType, "Endpoint[IN]");
  else
    $sformat(s_txnType, "Endpoint[UNKNOWN]");

  $sformat(s_data, "data=0x%0h, nBytes=%0d", o_et0Data, o_et0Data_nBytes);

  $display("INFO:t%0t:%m: %s sent.", $time, s_txnType, s_data);

  if (o_txnType[2]) begin
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

    $sformat(s_wValue, "");
    case (bRequest)
      BREQUEST_GET_STATUS:        $sformat(s_bRequest, "GET_STATUS");
      BREQUEST_CLEAR_FEATURE:     $sformat(s_bRequest, "CLEAR_FEATURE");
      BREQUEST_SET_STATUS:        $sformat(s_bRequest, "SET_STATUS");
      BREQUEST_SET_ADDRESS:       $sformat(s_bRequest, "SET_ADDRESS");
      BREQUEST_GET_DESCRIPTOR: begin
        $sformat(s_bRequest, "GET_DESCRIPTOR");
        case (wValue[15:8])
          BDESCRIPTORTYPE_DEVICE:         $sformat(s_wValue, " DEVICE");
          BDESCRIPTORTYPE_CONFIGURATION:  $sformat(s_wValue, " CONFIG");
          BDESCRIPTORTYPE_STRING:         $sformat(s_wValue, " STRING");
          BDESCRIPTORTYPE_INTERFACE:      $sformat(s_wValue, " INTERFACE");
          BDESCRIPTORTYPE_ENDPOINT:       $sformat(s_wValue, " ENDPOINT");
          BDESCRIPTORTYPE_DEVICEQUALIFIER:$sformat(s_wValue, " DEVICE_QUALIFIER");
          BDESCRIPTORTYPE_OTHERSPEED:     $sformat(s_wValue, " OTHER_SPEED");
          BDESCRIPTORTYPE_IFACEPOWER:     $sformat(s_wValue, " INTERFACE_POWER");
          BDESCRIPTORTYPE_CS_INTERFACE:   $sformat(s_wValue, " CS_INTERFACE");
          default:                        $sformat(s_wValue, " UNKNOWN");
        endcase
      end
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
    $display("  :wValue=0x%0h=%0d%s", wValue, wValue, s_wValue);
    $display("  :wIndex=0x%0h=%0d", wIndex, wIndex);
    $display("  :wLength=0x%0h=%0d", wLength, wLength);
  end

end : info


endmodule
