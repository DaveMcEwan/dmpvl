`include "dff.vh"
`include "asrt.vh"
`include "misc.vh"

/*
Control endpoint pair for either a generic serial device (/dev/ttyUSB*),
or an Abstract Control Model serial device (/dev/ttyACM*).
Generic device requires modprobe with VID:PID, and produces dmesg warning.
ACM device requires dummy endpoint, and may be interferred with by
modemmanager.

To get /dev/USB0 to appear you need to load the module with the exact
vendor/product ID to get the driver to recognise the device.
  modprobe usbserial vendor=0x1d50 product=0xf055

For a more permenant solution append to (or create)
/etc/udev/rules.d/99-dmpvl.rules, then run `udevadm control --reload-rules`:
  ATTRS{idVendor}=="1d50", ATTRS{idProduct}="fo55", \
    SYMLINK+="ttyUSB.dmpvl", \
    MODE="0666" \
    RUN+="modprobe usbserial vendor=0x1d50 product=0xf055"

Perhaps squat on 0525:a4a6 (NetChip Technology Inc, Linux-USB Serial Gadget) as
hinted at in kernel documentation.

See the kernel documentation under "Generic Serial Driver":
  https://www.kernel.org/doc/html/latest/usb/usb-serial.html

See this tutorial by Greg Kroah-Hartman:
  https://www.linuxjournal.com/article/6573
*/
module usbFullSpeedControlSerial #(
  parameter VENDOR_ID = 16'h1337,   // placeholder
  parameter PRODUCT_ID = 16'hf055,  // placeholder
  parameter ACM_NOT_GENERIC = 0,
  parameter MAX_PKT = 8
) (
  input  wire                       i_clk,
  input  wire                       i_rst,

  output wire [6:0]                 o_devAddr,

  output wire                       o_er0Stall,
  output wire                       o_et0Stall,

  output wire                       o_er0Ready,
  input  wire                       i_er0Valid,
  input  wire [8*MAX_PKT-1:0]       i_er0Data,
  input  wire [$clog2(MAX_PKT):0]   i_er0Data_nBytes,

  input  wire                       i_et0Ready, // High on receiving ACK/STALL
  output wire                       o_et0Valid,
  output wire [8*MAX_PKT-1:0]       o_et0Data,
  output wire [$clog2(MAX_PKT):0]   o_et0Data_nBytes,

  // flags {SETUP, OUT, IN}
  input  wire [2:0]                 i_txnType
);

`include "usbSpec.vh"

localparam DATA_W = 8*MAX_PKT;
localparam NBYTES_W = $clog2(MAX_PKT)+1;

wire er_accepted = o_er0Ready && i_er0Valid;
wire et_accepted = i_et0Ready && o_et0Valid;


// https://en.wikipedia.org/wiki/USB_(Communications)#Setup_packet
wire [ 4:0] bmRequestTypeRecipient  = i_er0Data[4:0];
wire [ 1:0] bmRequestTypeType       = i_er0Data[6:5];
wire        bmRequestTypeDirection  = i_er0Data[7];
wire [ 7:0] bRequest                = i_er0Data[15:8];
wire [15:0] wValue                  = i_er0Data[31:16];
wire [15:0] wIndex                  = i_er0Data[47:32];
wire [15:0] wLength                 = i_er0Data[63:48];

// {{{ Control Transfer flags

/*
A Control Transfer has either 2 or 3 stages, as one of 3 types:
  - Setup, Status
    - No data stage.
    - Standard Device Requents (bRequest) with no data stage include:
      - CLEAR_FEATURE
      - SET_ADDRESS
      - SET_CONFIGURATION
      - SET_FEATURE
      - SET_INTERFACE
    - NOTE: Only SET_ADDRESS is does something here, but others must be
      accepted as supported.
    - The host will start an IN transaction for the Status stage.
      - Supported is indicated by sending a zero-length data[DATA1].
      - Unsupported is indicated by sending a handshake[STALL].

  - Setup, Read, Status
    - Read stage consists of IN transactions to transfer data from device to host.
    - bmRequestType.Direction is set
    - Standard Device Requents (bRequest) with Read stage include:
      - GET_CONFIGURATION
      - GET_DESCRIPTOR
      - GET_INTERFACE
      - GET_STATUS
    - NOTE: Only GET_DESCRIPTOR is supported here.
    - The host will start at least 1 IN transaction for the Read stage.
      - Supported is indicated by sending data.
      - Unsupported is indicated by sending a handshake[STALL].
    - When supported, the host will start an OUT transaction for the Status
      stage, with a zero-length data[DATA1] that the device must ACK.

  - Setup, Write, Status
    - Write stage consists of OUT transactions to transfer data from host to device.
    - Standard Device Requents (bRequest) with Write stage include:
      - SET_DESCRIPTOR
    - NOTE: None of these supported here.
    - The host will start an OUT transaction for the Write stage.
      - Supported is indicated by sending a handshake[ACK] or handshake[NAK] in
        response to the data[DATAx] packet(s).
      - Unsupported is indicated by sending a handshake[STALL] in response to
        the data[DATAx] packet(s).

The Setup stage is always a setup transaction:
  token[SETUP]<host>, data[DATA0]<host>, handshake[ACK]<device>
Accepting the data by sending the ACK begins the Control Transfer from the
device's point of view.

Even though the device may only support a couple of types of requests, it still
must abide by the Control Transfer protocol.
*/

// NOTE: Design/implementation can probably get away with less strict checks
// on zero-length signals.
wire beginCtrlTfr = i_txnType[2] && er_accepted;
wire rcvdZeroLengthOut = i_txnType[1] && er_accepted;// && (i_er0Data_nBytes == '0); NOTE: Host may misbehave
wire sentZeroLengthIn  = i_txnType[0] && et_accepted && (o_et0Data_nBytes == '0);

// NOTE: Host may send many requests in any order so just lower everything and
// use the most recent.

wire tfrNoData_raise = beginCtrlTfr && (wLength == '0);
wire tfrNoData_lower = sentZeroLengthIn || et0Stall_q || beginCtrlTfr;
`dff_nocg_srst(reg, tfrNoData, i_clk, i_rst, 1'b0)
always @*
  if (tfrNoData_raise)
    tfrNoData_d = 1'b1;
  else if (tfrNoData_lower)
    tfrNoData_d = 1'b0;
  else
    tfrNoData_d = tfrNoData_q;

wire tfrRead_raise = beginCtrlTfr && (wLength != '0) && bmRequestTypeDirection;
wire tfrRead_lower = rcvdZeroLengthOut || et0Stall_q || beginCtrlTfr;
`dff_nocg_srst(reg, tfrRead, i_clk, i_rst, 1'b0)
always @*
  if (tfrRead_raise)
    tfrRead_d = 1'b1;
  else if (tfrRead_lower)
    tfrRead_d = 1'b0;
  else
    tfrRead_d = tfrRead_q;

wire tfrWrite_raise = beginCtrlTfr && (wLength != '0) && !bmRequestTypeDirection;
wire tfrWrite_lower = sentZeroLengthIn || er0Stall_q || beginCtrlTfr;
`dff_nocg_srst(reg, tfrWrite, i_clk, i_rst, 1'b0)
always @*
  if (tfrWrite_raise)
    tfrWrite_d = 1'b1;
  else if (tfrWrite_lower)
    tfrWrite_d = 1'b0;
  else
    tfrWrite_d = tfrWrite_q;

wire [2:0] tfrFlags_q = {
  tfrNoData_q,
  tfrRead_q,
  tfrWrite_q
};
`asrt(tfrFlags_q, i_clk, !i_rst, $onehot0(tfrFlags_q))

// }}} Control Transfer flags

// {{{ Stall (Request Error) flags

/* 9.2.7 Request Error
When a request is received by a device that is not defined for the device, is
inappropriate for the current setting of the device, or has values that are not
compatible with the request, then a Request Error exists.
The device deals with the Request Error by returning a STALL PID in response to
the next Data stage transaction or in the Status stage of the message.
It is preferred that the STALL PID be returned at the next Data stage
transaction, as this avoids unnecessary bus activity.
*/
// Device does not know when STALL has been sent so flag must be kept high until
// The next transfer begins.
// NOTE: Cannot use dff_flag because raise must occur on beginCtrlTfr.
wire et0Stall_raise = tfrRead_raise && !supported;
wire et0Stall_lower = beginCtrlTfr;
`dff_nocg_srst(reg, et0Stall, i_clk, i_rst, 1'b0)
always @*
  if (et0Stall_raise)
    et0Stall_d = 1'b1;
  else if (et0Stall_lower)
    et0Stall_d = 1'b0;
  else
    et0Stall_d = et0Stall_q;
assign o_et0Stall = et0Stall_q;

wire er0Stall_raise = tfrWrite_raise && !supported;
wire er0Stall_lower = beginCtrlTfr;
`dff_nocg_srst(reg, er0Stall, i_clk, i_rst, 1'b0)
always @*
  if (er0Stall_raise)
    er0Stall_d = 1'b1;
  else if (er0Stall_lower)
    er0Stall_d = 1'b0;
  else
    er0Stall_d = er0Stall_q;
assign o_er0Stall = er0Stall_q;

// }}} Stall (Request Error) flags

/*
o_er0Ready must be high to ACK:
  - setup[DATA0] which begins Setup stage of all Control Transfers.
  - Zero-length out[DATA1] which ends Status stage of Read.
NOTE: No Write transfers are supported here.
*/
assign o_er0Ready =
  i_txnType[2] || // Accept Setup transaction by ACKing the setup[DATA0].
  tfrRead_q;      // Accept zero-length out[DATA1] which ends Status stage of Read.


localparam DEVICE_BLENGTH = 18;
localparam CONFIG_WTOTALLENGTH = ACM_NOT_GENERIC ?
  (9 + 9+5+5+4+5+7 + 9+7+7) : // =67
  (9+9+7+7);                  // =32

wire [8*DEVICE_BLENGTH-1:0] deviceDescriptor_rom;
wire [8*CONFIG_WTOTALLENGTH-1:0] configDescriptor_rom;
generate if (ACM_NOT_GENERIC) begin
  // Descriptors for Abstract Control Model driver (/dev/ttyACMx)

  assign deviceDescriptor_rom = { // {{{
    8'd1,                           // bNumConfigurations
    8'd0,                           // iSerialNumber
    8'd0,                           // iProduct
    8'd0,                           // iManufacturer
    16'h0000,                       // bcdDevice
    PRODUCT_ID`LSb(16),             // idProduct
    VENDOR_ID`LSb(16),              // idVendor
    MAX_PKT`LSb(8),                 // bMaxPacketSize0
    8'd0,                           // bDeviceProtocol (unused for CDC)
    8'd0,                           // bDeviceSubClass (unused for CDC)
    BASECLASS_CDCCTRL`LSb(8),       // bDeviceClass (Communications Device Class)
    16'h0200,                       // bcdUSB, USB 2.0
    BDESCRIPTORTYPE_DEVICE`LSb(8),  // bDescriptorType
    DEVICE_BLENGTH`LSb(8)           // bLength
  }; // }}} deviceDescriptor_rom

  assign configDescriptor_rom = { // {{{
    // {{{ CDC-ACM-DATA interface

    // Endpoint descriptor, USB spec 9.6.6
    8'd0,                             // bInterval, Ignored for full-speed bulk endpoints.
    MAX_PKT`LSb(16),                  // wMaxPacketSize
    ENDPTYPE_BULK`LSb(8),             // bmAttributes
    8'd1 | 8'h80,                     // bEndpointAddress, CDC_TX_ENDPOINT=1
    BDESCRIPTORTYPE_ENDPOINT`LSb(8),  // bDescriptorType
    8'd7,                             // bLength

    // Endpoint descriptor, USB spec 9.6.6
    8'd0,                             // bInterval, Ignored for full-speed bulk endpoints.
    MAX_PKT`LSb(16),                  // wMaxPacketSize
    ENDPTYPE_BULK`LSb(8),             // bmAttributes
    8'd1,                             // bEndpointAddress, CDC_RX_ENDPOINT=1
    BDESCRIPTORTYPE_ENDPOINT`LSb(8),  // bDescriptorType
    8'd7,                             // bLength

    // Interface descriptor, USB spec 9.6.5
    8'd0,                             // iInterface
    8'd0,                             // bInterfaceProtocol
    8'd0,                             // bInterfaceSubClass
    BASECLASS_CDCDATA`LSb(8),         // bInterfaceClass
    8'd2,                             // bNumEndpoints
    8'd0,                             // bAlternateSetting
    8'd1,                             // bInterfaceNum
    BDESCRIPTORTYPE_INTERFACE`LSb(8), // bDescriptorType
    8'd9,                             // bLength

    // }}} CDC-ACM-DATA interface

    // {{{ CDC-ACM-CTRL interface

    // Endpoint descriptor, USB spec 9.6.6
    8'd255,                               // bInterval // 255ms
    MAX_PKT`LSb(16),                      // wMaxPacketSize
    ENDPTYPE_INTERRUPT`LSb(8),            // bmAttributes
    8'd2 | 8'h80,                         // bEndpointAddress, CDC_ACM_ENDPOINT=2
    BDESCRIPTORTYPE_ENDPOINT`LSb(8),      // bDescriptorType
    8'd7,                                 // bLength

    // Union Functional Descriptor, CDC Spec 5.2.3.8, Table 33
    8'd1, // bSlaveInterface0, Other interface is slave.
    8'd0, // bMasterInterface, This interface (bInterfaceNum=0) is master, despite doing nothing.
    BDESCRIPTORSUBTYPE_CDC_UNION`LSb(8),  // bDescriptorSubtype
    BDESCRIPTORTYPE_CS_INTERFACE`LSb(8),  // bDescriptorType
    8'd5,                                 // bFunctionLength

    // Abstract Control Management Functional Descriptor, CDC Spec 5.2.3.3, Table 28
    8'd0, // bmCapabilities, No support for GET_LINE_CODING.
    BDESCRIPTORSUBTYPE_CDC_ACM`LSb(8),    // bDescriptorSubtype
    BDESCRIPTORTYPE_CS_INTERFACE`LSb(8),  // bDescriptorType
    8'd4,                                 // bFunctionLength

    // Call Management Functional Descriptor, CDC Spec 5.2.3.2, Table 27
    8'd1,                                 // bDataInterface
    8'd0, // bmCapabilities, Handle call management in device so no OS "helpfulness".
    BDESCRIPTORSUBTYPE_CDC_CALLMGMT`LSb(8),// bDescriptorSubtype
    BDESCRIPTORTYPE_CS_INTERFACE`LSb(8),  // bDescriptorType
    8'd5,                                 // bFunctionLength

    // CDC Header Functional Descriptor, CDC Spec 5.2.3.1, Table 26
    16'h0110, // bcdCDC CDC spec version 1.1
    BDESCRIPTORSUBTYPE_CDC_HEADER`LSb(8), // bDescriptorSubtype
    BDESCRIPTORTYPE_CS_INTERFACE`LSb(8),  // bDescriptorType
    8'd5,                                 // bFunctionLength

    // Interface descriptor, USB spec 9.6.5
    // NOTE: This uses er2 but that isn't required to be hooked up to anything.
    8'd0,                                 // iInterface
    8'd0,                                 // bInterfaceProtocol (0=?, 1=AT Commands: V.250 etc)
    CDC_IFACE_SUBCLASS_ACM`LSb(8),        // bInterfaceSubClass (Abstract Control Model)
    BASECLASS_CDCCTRL`LSb(8),             // bInterfaceClass
    8'd1,                                 // bNumEndpoints
    8'd0,                                 // bAlternateSetting
    8'd0,                                 // bInterfaceNum
    BDESCRIPTORTYPE_INTERFACE`LSb(8),     // bDescriptorType
    8'd9,                                 // bLength

    // }}} CDC-ACM-CTRL interface

    8'd50,                                // bMaxPower, 50*2mA=100mA
    8'hC0,                                // bmAttributes, Bus+Self powered
    8'd0,                                 // iConfiguration
    8'd1,                                 // bConfigurationValue
    8'd2,                                 // bNumInterfaces
    CONFIG_WTOTALLENGTH`LSb(16),          // wTotalLength
    BDESCRIPTORTYPE_CONFIGURATION`LSb(8), // bDescriptorType
    8'd9                                  // bLength
  }; // }}} configDescriptor_rom

end else begin
  // Descriptors for usbserial driver (/dev/ttyUSBx)

  assign deviceDescriptor_rom = { // {{{
    8'd1,                               // bNumConfigurations
    8'd0,                               // iSerialNumber
    8'd0,                               // iProduct
    8'd0,                               // iManufacturer
    16'h0000,                           // bcdDevice
    PRODUCT_ID`LSb(16),                 // idProduct
    VENDOR_ID`LSb(16),                  // idVendor
    MAX_PKT`LSb(8),                     // bMaxPacketSize0
    8'd0,                               // bDeviceProtocol
    8'd0,                               // bDeviceSubClass
    BASECLASS_UNKNOWN`LSb(8),           // bDeviceClass, Use interface descriptor.
    16'h0200,                           // bcdUSB, USB 2.0
    BDESCRIPTORTYPE_DEVICE`LSb(8),      // bDescriptorType
    DEVICE_BLENGTH`LSb(8)               // bLength
  }; // }}} deviceDescriptor_rom

  assign configDescriptor_rom = { // {{{
    // Endpoint descriptor, USB spec 9.6.6
    8'd0,                               // bInterval, Ignored for full-speed bulk endpoints.
    MAX_PKT`LSb(16),                    // wMaxPacketSize
    ENDPTYPE_BULK`LSb(8),               // bmAttributes
    8'd1 | 8'h80,                       // bEndpointAddress, TX_ENDPOINT=1
    BDESCRIPTORTYPE_ENDPOINT`LSb(8),    // bDescriptorType
    8'd7,                               // bLength

    // Endpoint descriptor, USB spec 9.6.6
    8'd0,                               // bInterval, Ignored for full-speed bulk endpoints.
    MAX_PKT`LSb(16),                    // wMaxPacketSize
    ENDPTYPE_BULK`LSb(8),               // bmAttributes
    8'd1,                               // bEndpointAddress, RX_ENDPOINT=1
    BDESCRIPTORTYPE_ENDPOINT`LSb(8),    // bDescriptorType
    8'd7,                               // bLength

    // Interface descriptor, USB spec 9.6.5
    8'd0,                               // iInterface
    8'd0,                               // bInterfaceProtocol
    8'd0,                               // bInterfaceSubClass
    BASECLASS_VENDOR`LSb(8),            // bInterfaceClass, usbserial uses exact vendor:product
    8'd2,                               // bNumEndpoints
    8'd0,                               // bAlternateSetting
    8'd0,                               // bInterfaceNum
    BDESCRIPTORTYPE_INTERFACE`LSb(8),   // bDescriptorType
    8'd9,                               // bLength

    8'd50,                                // bMaxPower, 50*2mA=100mA
    8'hC0,                                // bmAttributes, Bus+Self powered
    8'd0,                                 // iConfiguration
    8'd1,                                 // bConfigurationValue
    8'd1,                                 // bNumInterfaces
    CONFIG_WTOTALLENGTH`LSb(16),          // wTotalLength
    BDESCRIPTORTYPE_CONFIGURATION`LSb(8), // bDescriptorType
    8'd9                                  // bLength
  }; // }}} configDescriptor_rom

end endgenerate

// {{{ Supported commands

/* 9.4.3 Get Descriptor
This request returns the specified descriptor if the descriptor exists.

bmRequestType | bRequest        | wValue      | wIndex    | wLength     | Data
--------------+-----------------+-------------+-----------+-------------+-----
8'b10000000   | GET_DESCRIPTOR  | Descriptor  | Zero or   | Descriptor  | Descriptor
              |                 | Type and    | Language  | Length      |
              |                 | Descriptor  | ID        |             |
              |                 | Index       |           |             |

The wValue field specifies the descriptor type in the high byte and the
descriptor index in the low byte.
The descriptor index is used to select a specific descriptor (only for
configuration and string descriptors) when several descriptors of the same type
are implemented in a device.
For example, a device can implement several configuration descriptors.
For other standard descriptors that can be retrieved via a GetDescriptor()
request, a descriptor index of zero must be used.

The wIndex field specifies the Language ID for string descriptors or is reset
to zero for other descriptors.

The wLength field specifies the number of bytes to return.
If the descriptor is longer than the wLength field, only the initial bytes of
the descriptor are returned.
If the descriptor is shorter than the wLength field, the device indicates the
end of the control transfer by sending a short packet when further data is
requested.
A short packet is defined as a packet shorter than the maximum payload size or
a zero length data packet.
*/
wire supportedDescriptor =
  (wValue[15:8] == BDESCRIPTORTYPE_DEVICE) ||
  (wValue[15:8] == BDESCRIPTORTYPE_CONFIGURATION);

// Simple descriptor-select because only 2 are supported.
wire descriptor_deviceNotConfig = (wValue[15:8] == BDESCRIPTORTYPE_DEVICE);

// Only 2 control transfers are supported.
// The host will issue GET_DESCRIPTOR transfers while the device address is
// still 0, then issue SET_ADDRESS to set it up to something else.
// SET_ADDRESS is always terminated by in[DATA1].
// GET_DESCRIPTOR is always terminated by out[DATA1].
wire setAddress = (bRequest == BREQUEST_SET_ADDRESS);
wire getDescriptor = (bRequest == BREQUEST_GET_DESCRIPTOR);

wire supported =
  setAddress ||
  (getDescriptor && supportedDescriptor);

// }}} Supported commands

// {{{ SET_ADDRESS, o_devAddr

// SET_ADDRESS control transfer is finished with an out[DATA1] transaction which
// must be handshaked, so new device address cannot be applied until that ACK
// has been sent.
// Sticky flag raised at the end of NoData transfer, never lowered.
wire setAddress_raise = sentZeroLengthIn && setAddress;
`dff_flag(setAddress, i_clk, i_rst, setAddress_raise, 1'b0)

`dff_cg_srst(reg [6:0], devAddr, i_clk, tfrNoData_raise && setAddress, i_rst, '0)
always @* devAddr_d = wValue[6:0];
assign o_devAddr = setAddress_q ? devAddr_q : '0;

// }}} SET_ADDRESS, o_devAddr

`dff_nocg_srst(reg [4:0], nPktsSent, i_clk, beginCtrlTfr, '0)
always @*
  if (et_accepted)
    nPktsSent_d = nPktsSent_q + 1;
  else
    nPktsSent_d = nPktsSent_q;

/*
A request for a configuration descriptor returns the configuration descriptor,
all interface descriptors, and endpoint descriptors for all of the interfaces
in a single request.
The first interface descriptor follows the configuration descriptor.
The endpoint descriptors for the first interface follow the first interface
descriptor.
If there are additional interfaces, their interface descriptor and endpoint
descriptors follow the first interface's endpoint descriptors.
Class-specific and/or vendor-specific descriptors follow the standard
descriptors they extend or modify.
All devices must provide a device descriptor and at least one configuration
descriptor.
If a device does not support a requested descriptor, it responds with a
Request Error.
*/
// Mux ROM data onto o_et0Data.
assign o_et0Data = descriptor_deviceNotConfig ?
  deviceDescriptor_rom[nPktsSent_q*DATA_W +: DATA_W] :
  configDescriptor_rom[nPktsSent_q*DATA_W +: DATA_W];

// NOTE: Descriptors must be <128B.
wire [6:0] nBytesDescriptor = descriptor_deviceNotConfig ?
  DEVICE_BLENGTH`LSb(7) :
  CONFIG_WTOTALLENGTH`LSb(7);
// NOTE: Possible bug in Linux USB driver allows bits to be set in upper byte of
// wLength, same behaviour required in different form in VGWM design.
wire partialDescriptor = ({1'b0, nBytesDescriptor} < wLength`LSb(8));
`asrt(wLength, i_clk, !i_rst && beginCtrlTfr && !partialDescriptor, (wLength[15:7] == '0))

// NOTE: Only to meet timing when synthed.
`dff_cg_srst(reg [6:0], nBytesToSend, i_clk, beginCtrlTfr, i_rst, '0)
always @* nBytesToSend_d = partialDescriptor ? nBytesDescriptor : wLength[6:0];


// tfrNoData: Send zero length for Status stage.
// tfrRead: Send either NAK/STALL (handled by stall/valid signals) or descriptor.
//    nBytes should be either full packet, or remaining in descriptor.
// tfrWrite: Send zero length for Status stage.
reg [NBYTES_W-1:0] et0Data_nBytes;
always @*
  if (!tfrRead_q)
    et0Data_nBytes = '0;
  else if (nBytesToSend_q >= (nPktsSent_q * MAX_PKT + MAX_PKT))
    et0Data_nBytes = MAX_PKT`LSb(NBYTES_W);
  else
    et0Data_nBytes = {1'b0, nBytesToSend_q`LSb(NBYTES_W-1)};
assign o_et0Data_nBytes = et0Data_nBytes;

/*
Send data, not NAK/STALL for:
  - Read stage, until all data has been sent.
  - Zero-length in[DATA1] which ends Status stage of NoData.
  - Zero-length in[DATA1] which ends Status stage of Write (NOTE: unsupported here).
*/
assign o_et0Valid =
  (tfrRead_q && (nBytesToSend_q >= (nPktsSent_q*MAX_PKT))) ||
  tfrNoData_q ||
  tfrWrite_q; // NOTE: STALL overrides NAK when unsupported.

endmodule
