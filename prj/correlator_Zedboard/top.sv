
module top (
  input  GCLK, // (Y9 Zedboard.767-100-136.3)


`ifdef ZEDBOARD_FMC_XM105
  // Zedboard with XM105 in FMC with external USB electrical conversion board.
  // probes: J1 pins in order
  // pwm: J20 odd numbered pins.
  // {{{ usb electrical conversion VC707.*
  inout  FMC_LA28_P, // USB d+ (L29 LVCMOS18 Zedboard.J1.XX XM105.J16.5)
  inout  FMC_LA28_N, // USB d- (L30 LVCMOS18 Zedboard.J1.XX XM105.J16.7)
  output FMC_LA29_P, // usbpu  (T29 LVCMOS18 Zedboard.J1.XX XM105.J16.9)
  output FMC_LA29_N, // rstn   (T30 LVCMOS18 Zedboard.J1.XX XM105.J16.11)
  // }}} usb electrical conversion VC707.*
  // {{{ probes XM105.J1 odd
  input  FMC_LA00_CC_P,  // (K39 LVCMOS18 VC707.J17.XX XM105.J1.1)
  input  FMC_LA00_CC_N,  // (K40 LVCMOS18 VC707.J17.XX XM105.J1.3)
  input  FMC_LA01_CC_P,  // (J41 LVCMOS18 VC707.J17.XX XM105.J1.5)
  input  FMC_LA01_CC_N,  // (J40 LVCMOS18 VC707.J17.XX XM105.J1.7)
  input  FMC_LA02_P,     // (P41 LVCMOS18 VC707.J17.XX XM105.J1.9)
  input  FMC_LA02_N,     // (N41 LVCMOS18 VC707.J17.XX XM105.J1.11)
  input  FMC_LA03_P,     // (M42 LVCMOS18 VC707.J17.XX XM105.J1.13)
  input  FMC_LA03_N,     // (L42 LVCMOS18 VC707.J17.XX XM105.J1.15)
  input  FMC_LA04_P,     // (H40 LVCMOS18 VC707.J17.XX XM105.J1.17)
  input  FMC_LA04_N,     // (H41 LVCMOS18 VC707.J17.XX XM105.J1.19)
  input  FMC_LA05_P,     // (M41 LVCMOS18 VC707.J17.XX XM105.J1.21)
  input  FMC_LA05_N,     // (L41 LVCMOS18 VC707.J17.XX XM105.J1.23)
  input  FMC_LA06_P,     // (K42 LVCMOS18 VC707.J17.XX XM105.J1.25)
  input  FMC_LA06_N,     // (J42 LVCMOS18 VC707.J17.XX XM105.J1.27)
  input  FMC_LA07_P,     // (G41 LVCMOS18 VC707.J17.XX XM105.J1.29)
  input  FMC_LA07_N,     // (G42 LVCMOS18 VC707.J17.XX XM105.J1.31)
  input  FMC_LA08_P,     // (M37 LVCMOS18 VC707.J17.XX XM105.J1.33)
  input  FMC_LA08_N,     // (M38 LVCMOS18 VC707.J17.XX XM105.J1.35)
  input  FMC_LA09_P,     // (R42 LVCMOS18 VC707.J17.XX XM105.J1.37)
  input  FMC_LA09_N,     // (P42 LVCMOS18 VC707.J17.XX XM105.J1.39)
  // }}} probes XM105.J1 odd
  // {{{ probes XM105.J1 even
  input  FMC_LA10_P,     // (N38 LVCMOS18 VC707.J17.XX XM105.J1.2)
  input  FMC_LA10_N,     // (M39 LVCMOS18 VC707.J17.XX XM105.J1.4)
  input  FMC_LA11_P,     // (F40 LVCMOS18 VC707.J17.XX XM105.J1.6)
  input  FMC_LA11_N,     // (F41 LVCMOS18 VC707.J17.XX XM105.J1.8)
  input  FMC_LA12_P,     // (R40 LVCMOS18 VC707.J17.XX XM105.J1.10)
  input  FMC_LA12_N,     // (P40 LVCMOS18 VC707.J17.XX XM105.J1.12)
  input  FMC_LA13_P,     // (H39 LVCMOS18 VC707.J17.XX XM105.J1.14)
  input  FMC_LA13_N,     // (G39 LVCMOS18 VC707.J17.XX XM105.J1.16)
  input  FMC_LA14_P,     // (N39 LVCMOS18 VC707.J17.XX XM105.J1.18)
  input  FMC_LA14_N,     // (N40 LVCMOS18 VC707.J17.XX XM105.J1.20)
  input  FMC_LA15_P,     // (M36 LVCMOS18 VC707.J17.XX XM105.J1.22)
  input  FMC_LA15_N,     // (L37 LVCMOS18 VC707.J17.XX XM105.J1.24)
  input  FMC_LA16_P,     // (K37 LVCMOS18 VC707.J17.XX XM105.J1.26)
  input  FMC_LA16_N,     // (K38 LVCMOS18 VC707.J17.XX XM105.J1.28)
  input  FMC_LA17_CC_P,  // (L31 LVCMOS18 VC707.J17.XX XM105.J1.30)
  input  FMC_LA17_CC_N,  // (K32 LVCMOS18 VC707.J17.XX XM105.J1.32)
  input  FMC_LA18_CC_P,  // (M32 LVCMOS18 VC707.J17.XX XM105.J1.34)
  input  FMC_LA18_CC_N,  // (L32 LVCMOS18 VC707.J17.XX XM105.J1.36)
  input  FMC_LA19_P,     // (W30 LVCMOS18 VC707.J17.XX XM105.J1.38)
  input  FMC_LA19_N,     // (W31 LVCMOS18 VC707.J17.XX XM105.J1.40)
  // }}} probes XM105.J1 even
  // {{{ pwm XM105.J20 odd
  output FMC_LA20_P, // (Y29 LVCMOS18 VC707.J17.G21 XM105.J20.1)
  output FMC_LA20_N, // (Y30 LVCMOS18 VC707.J17.G22 XM105.J20.3)
  output FMC_LA21_P, // (N28 LVCMOS18 VC707.J17.H25 XM105.J20.5)
  output FMC_LA21_N, // (N29 LVCMOS18 VC707.J17.H26 XM105.J20.7)
  output FMC_LA22_P, // (R28 LVCMOS18 VC707.J17.G24 XM105.J20.9)
  output FMC_LA22_N, // (P28 LVCMOS18 VC707.J17.G25 XM105.J20.11)
  output FMC_LA23_P, // (P30 LVCMOS18 VC707.J17.D23 XM105.J20.13)
  output FMC_LA23_N  // (N31 LVCMOS18 VC707.J17.D24 XM105.J20.15)
  // }}} pwm XM105.J20 odd
`else
  // {{{ usb electrical conversion (extUsb face down in JA)
  inout  JA1, // USB OE       (Y11  LVCMOS18  Zedboard.Pmod.JA)
  inout  JA2, // USB d-       (AA11 LVCMOS18  Zedboard.Pmod.JA)
  output JA3, // USB d+       (Y10  LVCMOS18  Zedboard.Pmod.JA)
  output JA4, // usbpu/Vext   (AA9  LVCMOS18  Zedboard.Pmod.JA)
  // }}} usb electrical conversion
  // {{{ probes (Zedboard.SW* pushbuttons)
  input  BTNU,  // probe[0] (T18 LVCMOS18 Zedboard.BTNU)
  input  BTNR,  // probe[1] (R18 LVCMOS18 Zedboard.BTNR)
  input  BTND,  // probe[2] (R16 LVCMOS18 Zedboard.BTND)
  input  BTNL,  // probe[3] (N15 LVCMOS18 Zedboard.BTNL)
  // }}} probe
  // {{{ result pwm (Zedboard.LD* LEDs)
  output LD0, // (T22 LVCMOS18 Zedboard.LD0)
  output LD1  // (T21 LVCMOS18 Zedboard.LD1)
  // }}} result pwm
`endif
);
wire i_pin_gclk_100MHz = GCLK;
wire o_pin_usbpu = 1'b1;
wire b_pin_usb_p;
wire b_pin_usb_n;
wire o_pin_usb_oe;
`ifdef ZEDBOARD_FMC_XM105
  localparam N_PROBE  = 40;
  localparam N_ENGINE = 8;

  assign b_pin_usb_p = FMC_LA28_P;
  assign b_pin_usb_n = FMC_LA28_N;
  assign FMC_LA29_P = o_pin_usbpu;

  wire [N_PROBE-1:0] i_pin_probe = {
  // {{{ XM105.J1
  FMC_LA19_N,
  FMC_LA09_N,
  FMC_LA19_P,
  FMC_LA09_P,
  FMC_LA18_CC_N,
  FMC_LA08_N,
  FMC_LA18_CC_P,
  FMC_LA08_P,
  FMC_LA17_CC_N,
  FMC_LA07_N,
  FMC_LA17_CC_P,
  FMC_LA07_P,
  FMC_LA16_N,
  FMC_LA06_N,
  FMC_LA16_P,
  FMC_LA06_P,
  FMC_LA15_N,
  FMC_LA05_N,
  FMC_LA15_P,
  FMC_LA05_P,
  FMC_LA14_N,
  FMC_LA04_N,
  FMC_LA14_P,
  FMC_LA04_P,
  FMC_LA13_N,
  FMC_LA03_N,
  FMC_LA13_P,
  FMC_LA03_P,
  FMC_LA12_N,
  FMC_LA02_N,
  FMC_LA12_P,
  FMC_LA02_P,
  FMC_LA11_N,
  FMC_LA01_CC_N,
  FMC_LA11_P,
  FMC_LA01_CC_P,
  FMC_LA10_N,
  FMC_LA00_CC_N,
  FMC_LA10_P,
  FMC_LA00_CC_P
  // }}} XM105.J1
  };

  wire [N_ENGINE-1:0] o_pin_pwm;
  assign {
    FMC_LA23_N,
    FMC_LA23_P,
    FMC_LA22_N,
    FMC_LA22_P,
    FMC_LA21_N,
    FMC_LA21_P,
    FMC_LA20_N,
    FMC_LA20_P
  } = o_pin_pwm;
`else
  localparam N_PROBE  = 4;
  localparam N_ENGINE = 2;

  assign JA1 = o_pin_usb_oe;
  assign b_pin_usb_n = JA2;
  assign b_pin_usb_p = JA3;
  assign JA4 = o_pin_usbpu;

  wire [N_PROBE-1:0] i_pin_probe = {
    BTNL,
    BTND,
    BTNR,
    BTNU
  };

  wire [N_ENGINE-1:0] o_pin_pwm;
  assign {
    LD1,
    LD0
  } = o_pin_pwm;
`endif

wire clk_48MHz;
wire pllLocked;
pll48 u_pll48 (
  .i_clk_100MHz   (i_pin_gclk_100MHz),
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


wire [N_ENGINE-1:0] resultPwm;
usbfsBpCorrelator #(
  .USBFS_VIDPID_SQUAT     (1),
  .USBFS_ACM_NOT_GENERIC  (1),
  .USBFS_MAX_PKT          (16), // in {8,16,32,64}. wMaxPacketSize
  .N_PROBE                (N_PROBE),
  .N_ENGINE               (N_ENGINE),
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
assign o_pin_usb_oe = usbOutputEnable;

assign o_pin_pwm = resultPwm;

endmodule
