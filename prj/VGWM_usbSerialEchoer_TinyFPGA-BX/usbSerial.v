/*
This module was originally tinyfpga_bootloader.v in Luke Valent's code, and
modified by Lawrie Griffiths, then David Things, before this version.
It creates the endpoint modules and the protocol engine to run things.
Whereas the original creates a SPI bridge, this one creates a UART bridge.

General note:
USB communications happen over endpoints.
OUT endpoints are out with respect to the *host*, and IN endpoints are in with
respect to the *host*.
*/

// Top level module creates the end points clusters, (usb_serial_ctrl_ep,
// usb_uart_bridge_ep) and the main protocol engine (u_usbFsPe - passing in the
// in (3) and out (2) count, along with the actual usb signal lines).
// All the endpoint signals are connected to the protocol engine.
// The serial endpoint cluster and the control endpoint cluster have two
// endpoints each - 1x in, 1x out.

module usbSerial (
  input  wire         i_clk_48MHz,
  input  wire         i_rst,

  output wire         o_usbTx_p,
  output wire         o_usbTx_n,
  output wire         o_usbTxEn,
  input  wire         i_usbRx_p,
  input  wire         i_usbRx_n,

  // Into the module, out of the device, into the host.
  input  wire [7:0]   i_uartIn_data,
  input  wire         i_uartIn_valid,
  output wire         o_uartIn_ready,

  // Out of the host, into the device, out of the module.
  output wire [7:0]   o_uartOut_data,
  output wire         o_uartOut_valid,
  input  wire         i_uartOut_ready
);

wire [6:0] devAddr;
wire [7:0] outEp_data;

wire ctrl_outEp_req;
wire ctrl_outEp_grant;
wire ctrl_outEp_dataAvail;
wire ctrl_outEp_setup;
wire ctrl_outEp_dataGet;
wire ctrl_outEp_stall;
wire ctrl_outEp_acked;

wire ctrl_inEp_req;
wire ctrl_inEp_grant;
wire ctrl_inEp_dataFree;
wire ctrl_inEp_dataPut;
wire [7:0] ctrl_inEp_data;
wire ctrl_inEp_dataDone;
wire ctrl_inEp_stall;
wire ctrl_inEp_acked;

wire serial_outEp_req;
wire serial_outEp_grant;
wire serial_outEp_dataAvail;
wire serial_outEp_setup; // unused
wire serial_outEp_dataGet;
wire serial_outEp_stall;
wire serial_outEp_acked;

wire serial_inEp_req;
wire serial_inEp_grant;
wire serial_inEp_dataFree;
wire serial_inEp_dataPut;
wire [7:0] serial_inEp_data;
wire serial_inEp_dataDone;
wire serial_inEp_stall;
wire serial_inEp_acked;

localparam MAX_OUT_PACKET_SIZE = 8; // Must be in {8,16,32}
localparam MAX_IN_PACKET_SIZE = 8; // Must be in {8,16,32}

usbCtrlSerial #(
  .MAX_OUT_PACKET_SIZE  (MAX_OUT_PACKET_SIZE),
  .MAX_IN_PACKET_SIZE   (MAX_IN_PACKET_SIZE)
) u_ctrlEp (
  .i_clk              (i_clk_48MHz),
  .i_rst              (i_rst),
  .o_devAddr          (devAddr),

  .o_outEp_req        (ctrl_outEp_req),
  .i_outEp_grant      (ctrl_outEp_grant),
  .i_outEp_dataAvail  (ctrl_outEp_dataAvail),
  .i_outEp_setup      (ctrl_outEp_setup),
  .o_outEp_dataGet    (ctrl_outEp_dataGet),
  .i_outEp_data       (outEp_data),
  .i_outEp_acked      (ctrl_outEp_acked),

  .o_inEp_req         (ctrl_inEp_req),
  .i_inEp_grant       (ctrl_inEp_grant),
  .i_inEp_dataFree    (ctrl_inEp_dataFree),
  .o_inEp_dataPut     (ctrl_inEp_dataPut),
  .o_inEp_data        (ctrl_inEp_data),
  .o_inEp_dataDone    (ctrl_inEp_dataDone),
  .o_inEp_stall       (ctrl_inEp_stall),
  .i_inEp_acked       (ctrl_inEp_acked)
);

usbEpBridge u_usbEpBridge (
  .i_clk              (i_clk_48MHz),
  .i_rst              (i_rst),

  .o_outEp_req        (serial_outEp_req),
  .i_outEp_grant      (serial_outEp_grant),
  .i_outEp_dataAvail  (serial_outEp_dataAvail),
  .i_outEp_setup      (serial_outEp_setup), // unused
  .o_outEp_dataGet    (serial_outEp_dataGet),
  .i_outEp_data       (outEp_data),
  .i_outEp_acked      (serial_outEp_acked), // unused

  .o_inEp_req         (serial_inEp_req),
  .i_inEp_grant       (serial_inEp_grant),
  .i_inEp_dataFree    (serial_inEp_dataFree),
  .o_inEp_dataPut     (serial_inEp_dataPut),
  .o_inEp_data        (serial_inEp_data),
  .o_inEp_dataDone    (serial_inEp_dataDone),
  .o_inEp_stall       (serial_inEp_stall),
  .i_inEp_acked       (serial_inEp_acked),

  .i_uartIn_data      (i_uartIn_data),
  .i_uartIn_valid     (i_uartIn_valid),
  .o_uartIn_ready     (o_uartIn_ready),

  .o_uartOut_data     (o_uartOut_data),
  .o_uartOut_valid    (o_uartOut_valid),
  .i_uartOut_ready    (i_uartOut_ready)
);

usbPe #(
  .N_EP_OUT   (2),
  .N_EP_IN    (2),
  .MAX_OUT_PACKET_SIZE  (MAX_OUT_PACKET_SIZE),
  .MAX_IN_PACKET_SIZE   (MAX_IN_PACKET_SIZE)
) u_ussPe (
  .i_clk              (i_clk_48MHz),
  .i_rst              (i_rst),

  .i_devAddr          (devAddr),

  .i_outEp_req        ({serial_outEp_req,         ctrl_outEp_req}),
  .o_outEp_grant      ({serial_outEp_grant,       ctrl_outEp_grant}),
  .o_outEp_dataAvail  ({serial_outEp_dataAvail,   ctrl_outEp_dataAvail}),
  .o_outEp_setup      ({serial_outEp_setup,       ctrl_outEp_setup}),
  .i_outEp_dataGet    ({serial_outEp_dataGet,     ctrl_outEp_dataGet}),
  .o_outEp_data       (outEp_data),
  .o_outEp_acked      ({serial_outEp_acked,       ctrl_outEp_acked}),

  /* reminder: Unused 3rd endpoint to do nothing for ACM control interface.
               The cdc_acm driver doesn't seem to mind if this does nothing.
  wire nak_inEp_grant;
  wire nak_inEp_dataFree;
  wire nak_inEp_acked;
  .N_EP_IN(3)
  .i_inEp_req         ({1'b0,               serial_inEp_req,        ctrl_inEp_req}),
  .o_inEp_grant       ({nak_inEp_grant,     serial_inEp_grant,      ctrl_inEp_grant}),
  .o_inEp_dataFree    ({nak_inEp_dataFree,  serial_inEp_dataFree,   ctrl_inEp_dataFree}),
  .i_inEp_dataPut     ({1'b0,               serial_inEp_dataPut,    ctrl_inEp_dataPut}),
  .i_inEp_data        ({8'b0,               serial_inEp_data[7:0],  ctrl_inEp_data[7:0]}),
  .i_inEp_dataDone    ({1'b0,               serial_inEp_dataDone,   ctrl_inEp_dataDone}),
  .i_inEp_stall       ({1'b0,               serial_inEp_stall,      ctrl_inEp_stall}),
  .o_inEp_acked       ({nak_inEp_acked,     serial_inEp_acked,      ctrl_inEp_acked}),
  */

  .i_inEp_req         ({serial_inEp_req,        ctrl_inEp_req}),
  .o_inEp_grant       ({serial_inEp_grant,      ctrl_inEp_grant}),
  .o_inEp_dataFree    ({serial_inEp_dataFree,   ctrl_inEp_dataFree}),
  .i_inEp_dataPut     ({serial_inEp_dataPut,    ctrl_inEp_dataPut}),
  .i_inEp_data        ({serial_inEp_data[7:0],  ctrl_inEp_data[7:0]}),
  .i_inEp_dataDone    ({serial_inEp_dataDone,   ctrl_inEp_dataDone}),
  .i_inEp_stall       ({serial_inEp_stall,      ctrl_inEp_stall}),
  .o_inEp_acked       ({serial_inEp_acked,      ctrl_inEp_acked}),

  .o_usbTx_p          (o_usbTx_p),
  .o_usbTx_n          (o_usbTx_n),
  .o_usbTxEn          (o_usbTxEn),
  .i_usbRx_p          (i_usbRx_p),
  .i_usbRx_n          (i_usbRx_n)
);

endmodule
