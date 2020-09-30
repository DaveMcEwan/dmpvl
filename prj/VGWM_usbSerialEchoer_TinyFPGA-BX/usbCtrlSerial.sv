`include "dff.svh"
`include "usbSpec.svh"

//  Contains all the USB setup logic.
//  Two endpoint interfaces (1x IN, 1x OUT).
//  Vendor 0x1D50, Product 0x6130.

module usbCtrlSerial #(
  parameter MAX_OUT_PACKET_SIZE = 8, // Must be in {8,16,32}
  parameter MAX_IN_PACKET_SIZE = 32 // Must be in {8,16,32}
) (
  input  wire         i_clk,
  input  wire         i_rst,
  output wire [6:0]   o_devAddr, // Device address, assigned by host.

  // out endpoint interface
  output wire         o_outEp_req,
  input  wire         i_outEp_grant,
  input  wire         i_outEp_dataAvail,
  input  wire         i_outEp_setup,
  output wire         o_outEp_dataGet,
  input  wire [7:0]   i_outEp_data,
  input  wire         i_outEp_acked,

  // in endpoint interface
  output wire         o_inEp_req,
  input  wire         i_inEp_grant,
  input  wire         i_inEp_dataFree,
  output wire         o_inEp_dataPut,
  output wire [7:0]   o_inEp_data,
  output wire         o_inEp_dataDone,
  output wire         o_inEp_stall,
  input  wire         i_inEp_acked
);

localparam IDLE = 0;
localparam SETUP = 1;
localparam DATA_IN = 2;
localparam DATA_OUT = 3;
localparam STATUS_IN = 4;
localparam STATUS_OUT = 5;

`dff_nocg_srst(reg [5:0], ctrlXfr, i_clk, i_rst, IDLE)
`dff_nocg_srst(reg, saveDevAddr, i_clk, i_rst, 1'b0)
`dff_nocg_srst(reg [6:0], devAddr, i_clk, i_rst, 7'd0)
`dff_nocg_srst(reg [3:0], setupDataAddr, i_clk, i_rst, 4'd0)
`dff_nocg_norst(reg [6:0], newDevAddr, i_clk)
`dff_nocg_norst(reg [6:0], romAddr, i_clk)


reg [7:0] inEpData;
wire allDataSent;
wire setupStageEnd;
wire statusStageEnd;
wire sendZeroLengthDataPkt;
wire byteSent;
wire pktStart;
wire pktEnd;
wire setupPktStart;
wire inDataTransferDone;

(* mem2reg *) reg [7:0] rawSetupData_m [8];
wire [7:0] bmRequestType = rawSetupData_m[0];
wire [7:0] bRequest = rawSetupData_m[1];
wire [15:0] wValue = {rawSetupData_m[3], rawSetupData_m[2]};
wire [15:0] wIndex = {rawSetupData_m[5], rawSetupData_m[4]};
wire [15:0] wLength = {rawSetupData_m[7], rawSetupData_m[6]};
wire [7:0] wLength_0 = wLength[7:0];

// {{{ inEp_stall

// USB Spec 9.4
// If an unsupported or invalid request is made to a USB device, the device
// responds by indicating a stall condition on the pipe used for the request.
wire supportedDescriptor =
  (wValue[15:8] == BDESCRIPTORTYPE_CONFIGURATION) ||
  (wValue[15:8] == BDESCRIPTORTYPE_DEVICE);

`dff_nocg_norst(reg, inEp_stall, i_clk)
always @* inEp_stall_d =
  setupStageEnd &&
  (bRequest == BREQUEST_GET_DESCRIPTOR) &&
  !supportedDescriptor;

assign o_inEp_stall = inEp_stall_q;

// }}} inEp_stall

`dff_nocg_norst(reg, outEpDataValid, i_clk)
always @* outEpDataValid_d =
  i_outEp_dataAvail && i_outEp_grant;

edgeDetect u_detectPktStartEnd (
  .i_clk(i_clk),
  .i_x(i_outEp_dataAvail),
  .o_rise(pktStart),
  .o_fall(pktEnd),
  .o_either()
);

assign setupPktStart = pktStart && i_outEp_setup;

wire hasDataStage = |wLength_0;
wire hasOutDataStage = hasDataStage && !bmRequestType[7];
wire hasInDataStage = hasDataStage && bmRequestType[7];

edgeDetect u_detectInDataTransferDone (
  .i_clk(i_clk),
  .i_x(allDataSent),
  .o_rise(inDataTransferDone),
  .o_fall(),
  .o_either()
);

assign o_inEp_req = (ctrlXfr_q == DATA_IN) && !allDataSent;

assign o_inEp_dataPut =
  (ctrlXfr_q == DATA_IN) &&
  !allDataSent &&
  i_inEp_dataFree;

assign setupStageEnd = (ctrlXfr_q == SETUP) && pktEnd;

assign statusStageEnd =
  ((ctrlXfr_q == DATA_IN) && inEp_stall_q) ||
  ((ctrlXfr_q == STATUS_IN) && i_inEp_acked) ||
  ((ctrlXfr_q == STATUS_OUT) && i_outEp_acked);

assign sendZeroLengthDataPkt =
  ((ctrlXfr_q == SETUP) && pktEnd && !hasDataStage) ||
  ((ctrlXfr_q == DATA_OUT) && i_outEp_acked);

assign byteSent =
  (ctrlXfr_q == DATA_IN) &&
  !allDataSent &&
  i_inEp_grant &&
  i_inEp_dataFree;

always @* // {{{ ctrlXfr FSM
  case (ctrlXfr_q)
    IDLE:
      if (setupPktStart)
        ctrlXfr_d = SETUP;
      else
        ctrlXfr_d = IDLE;

    SETUP:
      if (pktEnd) begin
        if (hasInDataStage)
          ctrlXfr_d = DATA_IN;
        else if (hasOutDataStage)
          ctrlXfr_d = DATA_OUT;
        else
          ctrlXfr_d = STATUS_IN;
      end else begin
        ctrlXfr_d = SETUP;
      end

    DATA_IN:
      if (inEp_stall_q)
        ctrlXfr_d = IDLE;
      else if (i_inEp_acked && allDataSent)
        ctrlXfr_d = STATUS_OUT;
      else
        ctrlXfr_d = DATA_IN;

    DATA_OUT:
      if (i_outEp_acked)
        ctrlXfr_d = STATUS_IN;
      else
        ctrlXfr_d = DATA_OUT;

    STATUS_IN:
      if (i_inEp_acked)
        ctrlXfr_d = IDLE;
      else
        ctrlXfr_d = STATUS_IN;

    STATUS_OUT:
      if (i_outEp_acked)
        ctrlXfr_d = IDLE;
      else
        ctrlXfr_d = STATUS_OUT;

    default:
      ctrlXfr_d = IDLE;
  endcase // }}} ctrlXfr FSM

// We need to save the address after the status stage ends this is because
// the status stage token will still be using the old device address.
always @*
  if (setupStageEnd && (bRequest == BREQUEST_SET_ADDRESS))
    newDevAddr_d = wValue[6:0];
  else
    newDevAddr_d = newDevAddr_q;

// The default control endpoint gets assigned the device address.
always @*
  if (statusStageEnd && saveDevAddr_q)
    devAddr_d = newDevAddr_q;
  else
    devAddr_d = devAddr_q;

// We need to save the address after the status stage ends because the
// status stage token will still be using the old device address.
always @*
  if (statusStageEnd && saveDevAddr_q)
    saveDevAddr_d = 1'b0;
  else if (setupStageEnd && (bRequest == BREQUEST_SET_ADDRESS))
    saveDevAddr_d = 1'b1;
  else
    saveDevAddr_d = saveDevAddr_q;

always @*
  if (statusStageEnd)
    setupDataAddr_d = 4'd0;
  else if (i_outEp_setup && outEpDataValid_q)
    setupDataAddr_d = setupDataAddr_q + 4'd1;
  else
    setupDataAddr_d = setupDataAddr_q;

// i_outEp_setup remains high from when a SETUP token is received, until an OUT
// token is received.
always @ (posedge i_clk)
  if (i_outEp_setup && outEpDataValid_q)
    rawSetupData_m[setupDataAddr_q[2:0]] <= i_outEp_data;

wire getDescriptor_config =
  (bRequest == BREQUEST_GET_DESCRIPTOR) &&
  (wValue[15:8] == BDESCRIPTORTYPE_CONFIGURATION);

always @*
  if (statusStageEnd)
    romAddr_d = 7'd0;
  else if (byteSent)
    romAddr_d = romAddr_q + 7'd1;
  else if (setupStageEnd)
    romAddr_d = getDescriptor_config ? 7'h12 : 7'd0;
  else
    romAddr_d = romAddr_q;


// {{{ allDataSent

// There are only 2 descriptors sent, which have a fixed length of 18 or 67
// bytes so this only has to be large enough to fit those values.
`dff_nocg_srst(reg [6:0], romLength, i_clk, i_rst, '0)
`dff_nocg_srst(reg [6:0], nBytesSent, i_clk, i_rst, '0)

wire getDescriptorDevice =
  (bRequest == BREQUEST_GET_DESCRIPTOR) &&
  (wValue[15:8] == BDESCRIPTORTYPE_DEVICE);

wire getDescriptorConfiguration =
  (bRequest == BREQUEST_GET_DESCRIPTOR) &&
  (wValue[15:8] == BDESCRIPTORTYPE_CONFIGURATION);

always @*
  if (statusStageEnd)
    romLength_d = 'd0;
  else if (setupStageEnd && getDescriptorDevice)
    romLength_d = 'd18;
  else if (setupStageEnd && getDescriptorConfiguration)
    //romLength_d = 'd67; // /dev/ttyACM* configuration
    romLength_d = 'd32; // /dev/ttyUSB* configuration
  else
    romLength_d = romLength_q;

always @*
  if (statusStageEnd)
    nBytesSent_d = 'd0;
  else if (byteSent)
    nBytesSent_d = nBytesSent_q + 1;
  else
    nBytesSent_d = nBytesSent_q;

assign allDataSent =
  (nBytesSent_q == romLength_q) ||
  ({1'd0, nBytesSent_q} == wLength_0);

// }}} allDataSent

/*
always @* // {{{ inEpData (/dev/ttyACM*)
  case (romAddr_q)
    // Device descriptor, USB spec 9.6.1
    // http://wiki.openmoko.org/wiki/USB_Product_IDs
    // https://raw.githubusercontent.com/openmoko/openmoko-usb-oui/master/usb_product_ids.psv
    // Links working as of 2019-11-27
    'h000: inEpData = 8'd18;  // bLength
    'h001: inEpData = BDESCRIPTORTYPE_DEVICE; // bDescriptorType
    'h002: inEpData = 8'h00;  // bcdUSB[0] // USB 2.0
    'h003: inEpData = 8'h02;  // bcdUSB[1] // Binary Coded Decimal
    'h004: inEpData = BASECLASS_CDCCTRL; // bDeviceClass (Communications Device Class)
    'h005: inEpData = 8'd0;   // bDeviceSubClass (unused for CDC)
    'h006: inEpData = 8'd0;   // bDeviceProtocol (unused for CDC)
    'h007: inEpData = MAX_IN_PACKET_SIZE; // bMaxPacketSize0
    'h008: inEpData = 8'h50;  // idVendor[0] (openmoko, assigned to FOSS projects)
    'h009: inEpData = 8'h1d;  // idVendor[1]
    'h00A: inEpData = 8'h30;  // idProduct[0] (TinyFPGA bootloader, incorrect for generic UART)
    'h00B: inEpData = 8'h61;  // idProduct[1]
    'h00C: inEpData = 8'd0;   // bcdDevice[0] // Device release number
    'h00D: inEpData = 8'd0;   // bcdDevice[1] // Binary coded decimal
    'h00E: inEpData = 8'd0;   // iManufacturer  // Index of string descriptor
    'h00F: inEpData = 8'd0;   // iProduct       // Index of string descriptor
    'h010: inEpData = 8'd0;   // iSerialNumber  // Index of string descriptor
    'h011: inEpData = 8'd1;   // bNumConfigurations

    // Configuration descriptor, USB spec 9.6.2
    'h012: inEpData = 8'd9;   // bLength
    'h013: inEpData = BDESCRIPTORTYPE_CONFIGURATION; // bDescriptorType
    'h014: inEpData = 8'd67; // wTotalLength[0] (9+9+5+5+4+5+7+9+7+7)
    'h015: inEpData = 8'd0;  // wTotalLength[1]
    'h016: inEpData = 8'd2;  // bNumInterfaces
    'h017: inEpData = 8'd1;  // bConfigurationValue
    'h018: inEpData = 8'd0;  // iConfiguration  // Index of string descriptor
    'h019: inEpData = 'hC0;  // bmAttributes
    'h01A: inEpData = 8'd50; // bMaxPower

    // interface descriptor, USB spec 9.6.5, page 267-269, Table 9-12
    'h01B: inEpData = 8'd9;         // bLength
    'h01C: inEpData = BDESCRIPTORTYPE_INTERFACE; // bDescriptorType
    'h01D: inEpData = 8'd0;            // bInterfaceNumber
    'h01E: inEpData = 8'd0;            // bAlternateSetting
    'h01F: inEpData = 8'd1;            // bNumEndpoints
    'h020: inEpData = 8'd2;            // bInterfaceClass (Communications Device Class)
    'h021: inEpData = 8'd2;            // bInterfaceSubClass (Abstract Control Model)
    'h022: inEpData = 8'd0;            // bInterfaceProtocol (0 = ?, 1 = AT Commands: V.250 etc)
    'h023: inEpData = 8'd0;            // iInterface

    // CDC Header Functional Descriptor, CDC Spec 5.2.3.1, Table 26
    'h024: inEpData = 8'd5;         // bFunctionLength
    'h025: inEpData = 'h24;         // bDescriptorType
    'h026: inEpData = 'h00;         // bDescriptorSubtype
    'h027: inEpData = 'h10;
    'h028: inEpData = 'h01;         // bcdCDC

    // Call Management Functional Descriptor, CDC Spec 5.2.3.2, Table 27
    'h029: inEpData = 8'd5;         // bFunctionLength
    'h02A: inEpData = 'h24;         // bDescriptorType
    'h02B: inEpData = 'h01;         // bDescriptorSubtype
    'h02C: inEpData = 'h00;         // bmCapabilities
    'h02D: inEpData = 8'd1;            // bDataInterface

    // Abstract Control Management Functional Descriptor, CDC Spec 5.2.3.3, Table 28
    'h02E: inEpData = 8'd4;         // bFunctionLength
    'h02F: inEpData = 'h24;         // bDescriptorType
    'h030: inEpData = 'h02;         // bDescriptorSubtype
    'h031: inEpData = 'h00;         // bmCapabilities

    // Union Functional Descriptor, CDC Spec 5.2.3.8, Table 33
    'h032: inEpData = 8'd5;         // bFunctionLength
    'h033: inEpData = 'h24;         // bDescriptorType
    'h034: inEpData = 'h06;         // bDescriptorSubtype
    'h035: inEpData = 8'd0;            // bMasterInterface
    'h036: inEpData = 8'd1;            // bSlaveInterface0

    // endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
    'h037: inEpData = 8'd7;         // bLength
    'h038: inEpData = BDESCRIPTORTYPE_ENDPOINT; // bDescriptorType
    'h039: inEpData = 'd2 | 'h80;   // bEndpointAddress, CDC_ACM_ENDPOINT=2
    'h03A: inEpData = ENDPTYPE_INTERRUPT; // bmAttributes
    'h03B: inEpData = 8'd8;            // wMaxPacketSize[0]
    'h03C: inEpData = 8'd0;            // wMaxPacketSize[1]
    'h03D: inEpData = 8'd255;           // bInterval

    // interface descriptor, USB spec 9.6.5, page 267-269, Table 9-12
    'h03E: inEpData = 8'd9;         // bLength
    'h03F: inEpData = BDESCRIPTORTYPE_INTERFACE; // bDescriptorType
    'h040: inEpData = 8'd1;            // bInterfaceNumber
    'h041: inEpData = 8'd0;            // bAlternateSetting
    'h042: inEpData = 8'd2;            // bNumEndpoints
    'h043: inEpData = 'h0A;         // bInterfaceClass
    'h044: inEpData = 'h00;         // bInterfaceSubClass
    'h045: inEpData = 'h00;         // bInterfaceProtocol
    'h046: inEpData = 8'd0;            // iInterface

    // endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
    'h047: inEpData = 8'd7;         // bLength
    'h048: inEpData = BDESCRIPTORTYPE_ENDPOINT; // bDescriptorType
    'h049: inEpData = 8'd1;            // bEndpointAddress, CDC_RX_ENDPOINT=1
    'h04A: inEpData = ENDPTYPE_BULK; // bmAttributes
    'h04B: inEpData = MAX_IN_PACKET_SIZE; // wMaxPacketSize[0]
    'h04C: inEpData = 8'd0;            // wMaxPacketSize[1]
    'h04D: inEpData = 8'd0;            // bInterval

    // endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
    'h04E: inEpData = 8'd7;         // bLength
    'h04F: inEpData = BDESCRIPTORTYPE_ENDPOINT; // bDescriptorType
    'h050: inEpData = 'h01 | 'h80;  // bEndpointAddress, CDC_TX_ENDPOINT=1
    'h051: inEpData = ENDPTYPE_BULK; // bmAttributes
    'h052: inEpData = MAX_OUT_PACKET_SIZE; // wMaxPacketSize[0]
    'h053: inEpData = 8'd0;            // wMaxPacketSize[1]
    'h054: inEpData = 8'd0;            // bInterval

    // // LINE_CODING
    // 'h055: inEpData = 8'h80;         // dwDTERate[0] // 9600 baud
    // 'h056: inEpData = 8'h25;         // dwDTERate[1]
    // 'h057: inEpData = 8'h00;         // dwDTERate[2]
    // 'h058: inEpData = 8'h00;         // dwDTERate[3]
    // 'h059: inEpData = 8'd0;          // bCharFormat (1 stop bit)
    // 'h05A: inEpData = 8'd0;          // bParityType (None)
    // 'h05B: inEpData = 8'd8;          // bDataBits (8 bits)

    default: inEpData = 8'd0;
  endcase // }}} inEpData
*/
always @* // {{{ inEpData (/dev/ttyUSB*)
  case (romAddr_q)
    // Device descriptor, USB spec 9.6.1
    'h000: inEpData = 8'd18;  // bLength
    'h001: inEpData = BDESCRIPTORTYPE_DEVICE; // bDescriptorType
    'h002: inEpData = 8'h00;  // bcdUSB[0] // USB 2.0
    'h003: inEpData = 8'h02;  // bcdUSB[1]
    'h004: inEpData = BASECLASS_UNKNOWN; // bDeviceClass
    'h005: inEpData = 8'd0;   // bDeviceSubClass (unused for CDC)
    'h006: inEpData = 8'd0;   // bDeviceProtocol (unused for CDC)
    'h007: inEpData = MAX_IN_PACKET_SIZE; // bMaxPacketSize0
    'h008: inEpData = 8'h25;  // idVendor[0], 0525, NetChip Technology
    'h009: inEpData = 8'h05;  // idVendor[1]
    'h00A: inEpData = 8'ha6;  // idProduct[0], a4a6, Linux-USB Serial Gadget
    'h00B: inEpData = 8'ha4;  // idProduct[1]
    'h00C: inEpData = 8'd0;   // bcdDevice[0] // Device release number
    'h00D: inEpData = 8'd0;   // bcdDevice[1]
    'h00E: inEpData = 8'd0;   // iManufacturer
    'h00F: inEpData = 8'd0;   // iProduct
    'h010: inEpData = 8'd0;   // iSerialNumber
    'h011: inEpData = 8'd1;   // bNumConfigurations

    // Configuration descriptor, USB spec 9.6.2
    'h012: inEpData = 8'd9;   // bLength
    'h013: inEpData = BDESCRIPTORTYPE_CONFIGURATION; // bDescriptorType
    'h014: inEpData = 8'd32; // wTotalLength[0] (9+9+7+7)
    'h015: inEpData = 8'd0;  // wTotalLength[1]
    'h016: inEpData = 8'd1;  // bNumInterfaces
    'h017: inEpData = 8'd1;  // bConfigurationValue
    'h018: inEpData = 8'd0;  // iConfiguration
    'h019: inEpData = 'hC0;  // bmAttributes
    'h01A: inEpData = 8'd50; // bMaxPower

    // interface descriptor, USB spec 9.6.5, page 267-269, Table 9-12
    'h01B: inEpData = 8'd9; // bLength
    'h01C: inEpData = BDESCRIPTORTYPE_INTERFACE; // bDescriptorType
    'h01D: inEpData = 8'd0; // bInterfaceNumber
    'h01E: inEpData = 8'd0; // bAlternateSetting
    'h01F: inEpData = 8'd2; // bNumEndpoints
    'h020: inEpData = BASECLASS_VENDOR; // bInterfaceClass
    'h021: inEpData = 8'd0; // bInterfaceSubClass
    'h022: inEpData = 8'd0; // bInterfaceProtocol
    'h023: inEpData = 8'd0; // iInterface

    // endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
    'h024: inEpData = 8'd7; // bLength
    'h025: inEpData = BDESCRIPTORTYPE_ENDPOINT; // bDescriptorType
    'h026: inEpData = 8'd1; // bEndpointAddress, RX_ENDPOINT=1
    'h027: inEpData = ENDPTYPE_BULK; // bmAttributes
    'h028: inEpData = MAX_IN_PACKET_SIZE; // wMaxPacketSize[0]
    'h029: inEpData = 8'd0; // wMaxPacketSize[1]
    'h02A: inEpData = 8'd0; // bInterval

    // endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
    'h02B: inEpData = 8'd7; // bLength
    'h02C: inEpData = BDESCRIPTORTYPE_ENDPOINT; // bDescriptorType
    'h02D: inEpData = 'h01 | 'h80;  // bEndpointAddress, TX_ENDPOINT=1
    'h02E: inEpData = ENDPTYPE_BULK; // bmAttributes
    'h02F: inEpData = MAX_OUT_PACKET_SIZE; // wMaxPacketSize[0]
    'h030: inEpData = 8'd0; // wMaxPacketSize[1]
    'h031: inEpData = 8'd0; // bInterval

    default: inEpData = 8'd0;
  endcase // }}} inEpData


assign o_outEp_dataGet = i_outEp_dataAvail;

assign o_outEp_req = i_outEp_dataAvail;

assign o_inEp_dataDone =
  (inDataTransferDone && ctrlXfr_q == DATA_IN) ||
  sendZeroLengthDataPkt;

assign o_devAddr = devAddr_q;

assign o_inEp_data = inEpData;

endmodule
