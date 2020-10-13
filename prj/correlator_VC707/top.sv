
module top (
  input  SYSCLK_P, // (E19 LVDS U51.4)
  input  SYSCLK_N, // (E18 LVDS U51.5)

  inout  USER_SMA_GPIO_P, // USB d+ (AN31 LVCMOS18 J33.1)
  inout  USER_SMA_GPIO_N, // USB d- (AP31 LVCMOS18 J34.1)

  input  GPIO_SW_N,  // probe[0] (AR40 LVCMOS18 SW3.3)
  input  GPIO_SW_E,  // probe[1] (AU38 LVCMOS18 SW4.3)
  input  GPIO_SW_S,  // probe[2] (AP40 LVCMOS18 SW5.3)
  input  GPIO_SW_W,  // probe[3] (AW40 LVCMOS18 SW7.3)

  output GPIO_LED_0, // (AM39 LVCMOS18 DS2.2)
  output GPIO_LED_1  // (AN39 LVCMOS18 DS3.2)
);

wire i_pin_sysclk_p_200MHz = SYSCLK_P;
wire i_pin_sysclk_n_200MHz = SYSCLK_N;
wire b_pin_usb_p = USER_SMA_GPIO_P;
wire b_pin_usb_n = USER_SMA_GPIO_N;
wire [3:0] i_pin_probe = {
  GPIO_SW_W,
  GPIO_SW_S,
  GPIO_SW_E,
  GPIO_SW_N
};
wire [1:0] o_pin_pwm;
  assign GPIO_LED_0 = o_pin_pwm[0];
  assign GPIO_LED_1 = o_pin_pwm[1];

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


wire [1:0] resultPwm;
usbfsBpCorrelator #(
  .USBFS_VIDPID_SQUAT     (1),
  .USBFS_ACM_NOT_GENERIC  (1),
  .USBFS_MAX_PKT          (16), // in {8,16,32,64}. wMaxPacketSize
  .N_PROBE                (4),
  .N_ENGINE               (2),
  .MAX_WINDOW_LENGTH_EXP  (16),
  .MAX_SAMPLE_PERIOD_EXP  (15),
  .MAX_SAMPLE_JITTER_EXP  (8),
  .WINDOW_PRECISION       (8), // 1 < p <= MAX_WINDOW_LENGTH_EXP
  .METRIC_PRECISION       (16),
  .PKTFIFO_DEPTH          (50)
) u_usbfsBpCorrelator (
  .i_clk_48MHz        (clk_48MHz),
  .i_rst              (rst),
  .i_cg               (1'b1),

  // USB {d+, d-}, output enable.
  .i_dp               (usbRx_p),
  .i_dn               (usbRx_n),
  .o_dp               (usbTx_p),
  .o_dn               (usbTx_n),
  .o_oe               (usbOutputEnable),

  .i_probe            (i_pin_probe),

  .o_pwm              (resultPwm)
);


localparam LED_BLINKONLY = 0;
generate if (LED_BLINKONLY != 0) begin
  reg [23:0] ledCounter_q;
  always @(posedge clk_48MHz)
    if (rst)
      ledCounter_q <= 24'd0;
    else
      ledCounter_q <= ledCounter_q + 24'd1;
  assign o_pin_pwm = ledCounter_q[23:22];
end else begin
  assign o_pin_pwm = resultPwm;
end endgenerate

endmodule
