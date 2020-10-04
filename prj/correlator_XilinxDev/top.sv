
module top (
  input  SYSCLK_P, // (E19 LVDS U51.4)
  input  SYSCLK_N, // (E18 LVDS U51.5)

  inout  USER_SMA_GPIO_P, // USB d+ (AN31 LVCMOS18 J33.1)
  inout  USER_SMA_GPIO_N, // USB d- (AP31 LVCMOS18 J34.1)

  input  GPIO_SW_W,  // X-probe (AW40 LVCMOS18 SW7.3)
  input  GPIO_SW_E,  // Y-probe (AU38 LVCMOS18 SW4.3)

  output GPIO_LED_0  // (AM39 LVCMOS18 DS2.2)
);

wire i_pin_sysclk_p_200MHz = SYSCLK_P;
wire i_pin_sysclk_n_200MHz = SYSCLK_N;
wire b_pin_usb_p = USER_SMA_GPIO_P;
wire b_pin_usb_n = USER_SMA_GPIO_N;
wire i_pin_x = GPIO_SW_W;
wire i_pin_y = GPIO_SW_E;
wire o_pin_led; assign GPIO_LED_0 = o_pin_led;

wire clk_48MHz;
wire pllLocked;
pll48 u_pll48 (
  .i_clk_p_200MHz (i_pin_sysclk_p_200MHz),
  .i_clk_n_200MHz (i_pin_sysclk_n_200MHz),
  .o_clk_48MHz    (clk_48MHz),
  .o_locked       (pllLocked)
);

wire rst;
fpgaReset u_rst (
  .i_clk        (clk_48MHz),
  .i_pllLocked  (pllLocked),
  .o_rst        (rst)
);


wire usb_p;
wire usb_n;
wire usbOutputEnable; // Select GPIO input/output mode.
wire usbTx_p;
wire usbTx_n;
wire usbRx_p;
wire usbRx_n;

// Supply receiver with J line state when transmitting.
assign usbRx_p = usbOutputEnable ? 1'b1 : usb_p;
assign usbRx_n = usbOutputEnable ? 1'b0 : usb_n;

IOBUF #(
  .DRIVE        (16),
  .IBUF_LOW_PWR ("FALSE"),
  .IOSTANDARD   ("DEFAULT"),
  .SLEW         ("FAST")
) iobuf_usbp (
  .O  (usb_p),
  .I  (usbTx_p),
  .IO (b_pin_usb_p),
  .T  (!usbOutputEnable)
);

IOBUF #(
  .DRIVE        (16),
  .IBUF_LOW_PWR ("FALSE"),
  .IOSTANDARD   ("DEFAULT"),
  .SLEW         ("FAST")
) iobuf_usbn (
  .O  (usb_n),
  .I  (usbTx_n),
  .IO (b_pin_usb_n),
  .T  (!usbOutputEnable)
  );


wire [7:0] devToHost_data;
wire       devToHost_valid;
wire       devToHost_ready;
wire [7:0] hostToDev_data;
wire       hostToDev_valid;
wire       hostToDev_ready;

// NOTE: Setting MAX_PKT to 8 will actually *increase* LUT usage as yosys will
// convert all the memories to flops instead of using BRAMs.
usbfsSerial #(
  .ACM_NOT_GENERIC  (1),
  .MAX_PKT  (16) // in {8,16,32,64}
) u_dev (
  .i_clk_48MHz        (clk_48MHz),
  .i_rst              (rst),

  // USB {d+, d-}, output enable.
  .i_dp               (usbRx_p),
  .i_dn               (usbRx_n),
  .o_dp               (usbTx_p),
  .o_dn               (usbTx_n),
  .o_oe               (usbOutputEnable),

  .i_devToHost_data   (devToHost_data),
  .i_devToHost_valid  (devToHost_valid),
  .o_devToHost_ready  (devToHost_ready),

  .o_hostToDev_data   (hostToDev_data),
  .o_hostToDev_valid  (hostToDev_valid),
  .i_hostToDev_ready  (hostToDev_ready)
);

wire ledPwm;
correlator u_correlator (
  .i_clk              (clk_48MHz),
  .i_rst              (rst),
  .i_cg               (1'b1),

  .i_x                (i_pin_x),
  .i_y                (i_pin_y),

  .o_ledPwm           (ledPwm),

  .i_bp_data          (hostToDev_data),
  .i_bp_valid         (hostToDev_valid),
  .o_bp_ready         (hostToDev_ready),

  .o_bp_data          (devToHost_data),
  .o_bp_valid         (devToHost_valid),
  .i_bp_ready         (devToHost_ready)
);

localparam LED_BLINKONLY = 0;
generate if (LED_BLINKONLY != 0) begin
  reg [22:0] ledCounter_q;
  always @(posedge clk_48MHz)
    if (rst)
      ledCounter_q <= 23'd0;
    else
      ledCounter_q <= ledCounter_q + 23'd1;
  assign o_pin_led = ledCounter_q[22];
end else begin
  assign o_pin_led = ledPwm;
end endgenerate

endmodule
