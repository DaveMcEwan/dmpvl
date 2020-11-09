
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
  output JA1, // USB OE       (Y11  LVCMOS18  Zedboard.Pmod.JA)
  inout  JA2, // USB d-       (AA11 LVCMOS18  Zedboard.Pmod.JA)
  inout  JA3, // USB d+       (Y10  LVCMOS18  Zedboard.Pmod.JA)
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

// PS7 is required in Zynq target, even though it's not used.
  // {{{ ps7 wires
  // ps7 IO, common to almost every Zynq project.
  wire [14:0]   DDR_addr;
  wire [2:0]    DDR_ba;
  wire          DDR_cas_n;
  wire          DDR_ck_n;
  wire          DDR_ck_p;
  wire          DDR_cke;
  wire          DDR_cs_n;
  wire [3:0]    DDR_dm;
  wire [31:0]   DDR_dq;
  wire [3:0]    DDR_dqs_n;
  wire [3:0]    DDR_dqs_p;
  wire          DDR_odt;
  wire          DDR_ras_n;
  wire          DDR_reset_n;
  wire          DDR_we_n;
  wire          FIXED_IO_ddr_vrn;
  wire          FIXED_IO_ddr_vrp;
  wire [53:0]   FIXED_IO_mio;
  wire          FIXED_IO_ps_srstb;
  wire          FIXED_IO_ps_clk;
  wire          FIXED_IO_ps_porb;

  wire          ps7_o_M_AXI_GP0_ARVALID;
  wire          ps7_o_M_AXI_GP0_AWVALID;
  wire          ps7_o_M_AXI_GP0_BREADY;
  wire          ps7_o_M_AXI_GP0_RREADY;
  wire          ps7_o_M_AXI_GP0_WLAST;
  wire          ps7_o_M_AXI_GP0_WVALID;
  wire [11:0]   ps7_o_M_AXI_GP0_ARID;
  wire [11:0]   ps7_o_M_AXI_GP0_AWID;
  wire [11:0]   ps7_o_M_AXI_GP0_WID;
  wire [1:0]    ps7_o_M_AXI_GP0_ARBURST;
  wire [1:0]    ps7_o_M_AXI_GP0_ARLOCK;
  wire [2:0]    ps7_o_M_AXI_GP0_ARSIZE;
  wire [1:0]    ps7_o_M_AXI_GP0_AWBURST;
  wire [1:0]    ps7_o_M_AXI_GP0_AWLOCK;
  wire [2:0]    ps7_o_M_AXI_GP0_AWSIZE;
  wire [2:0]    ps7_o_M_AXI_GP0_ARPROT;
  wire [2:0]    ps7_o_M_AXI_GP0_AWPROT;
  wire [31:0]   ps7_o_M_AXI_GP0_ARADDR;
  wire [31:0]   ps7_o_M_AXI_GP0_AWADDR;
  wire [31:0]   ps7_o_M_AXI_GP0_WDATA;
  wire [3:0]    ps7_o_M_AXI_GP0_ARCACHE;
  wire [3:0]    ps7_o_M_AXI_GP0_ARLEN;
  wire [3:0]    ps7_o_M_AXI_GP0_ARQOS;
  wire [3:0]    ps7_o_M_AXI_GP0_AWCACHE;
  wire [3:0]    ps7_o_M_AXI_GP0_AWLEN;
  wire [3:0]    ps7_o_M_AXI_GP0_AWQOS;
  wire [3:0]    ps7_o_M_AXI_GP0_WSTRB;

  wire          ps7_i_M_AXI_GP0_ARREADY;
  wire          ps7_i_M_AXI_GP0_AWREADY;
  wire          ps7_i_M_AXI_GP0_BVALID;
  wire          ps7_i_M_AXI_GP0_RLAST;
  wire          ps7_i_M_AXI_GP0_RVALID;
  wire          ps7_i_M_AXI_GP0_WREADY;
  wire [11:0]   ps7_i_M_AXI_GP0_BID;
  wire [11:0]   ps7_i_M_AXI_GP0_RID;
  wire [1:0]    ps7_i_M_AXI_GP0_BRESP;
  wire [1:0]    ps7_i_M_AXI_GP0_RRESP;
  wire [31:0]   ps7_i_M_AXI_GP0_RDATA;

  wire          ps7_o_M_AXI_GP1_ARVALID;
  wire          ps7_o_M_AXI_GP1_AWVALID;
  wire          ps7_o_M_AXI_GP1_BREADY;
  wire          ps7_o_M_AXI_GP1_RREADY;
  wire          ps7_o_M_AXI_GP1_WLAST;
  wire          ps7_o_M_AXI_GP1_WVALID;
  wire [11:0]   ps7_o_M_AXI_GP1_ARID;
  wire [11:0]   ps7_o_M_AXI_GP1_AWID;
  wire [11:0]   ps7_o_M_AXI_GP1_WID;
  wire [1:0]    ps7_o_M_AXI_GP1_ARBURST;
  wire [1:0]    ps7_o_M_AXI_GP1_ARLOCK;
  wire [2:0]    ps7_o_M_AXI_GP1_ARSIZE;
  wire [1:0]    ps7_o_M_AXI_GP1_AWBURST;
  wire [1:0]    ps7_o_M_AXI_GP1_AWLOCK;
  wire [2:0]    ps7_o_M_AXI_GP1_AWSIZE;
  wire [2:0]    ps7_o_M_AXI_GP1_ARPROT;
  wire [2:0]    ps7_o_M_AXI_GP1_AWPROT;
  wire [31:0]   ps7_o_M_AXI_GP1_ARADDR;
  wire [31:0]   ps7_o_M_AXI_GP1_AWADDR;
  wire [31:0]   ps7_o_M_AXI_GP1_WDATA;
  wire [3:0]    ps7_o_M_AXI_GP1_ARCACHE;
  wire [3:0]    ps7_o_M_AXI_GP1_ARLEN;
  wire [3:0]    ps7_o_M_AXI_GP1_ARQOS;
  wire [3:0]    ps7_o_M_AXI_GP1_AWCACHE;
  wire [3:0]    ps7_o_M_AXI_GP1_AWLEN;
  wire [3:0]    ps7_o_M_AXI_GP1_AWQOS;
  wire [3:0]    ps7_o_M_AXI_GP1_WSTRB;

  wire          ps7_i_M_AXI_GP1_ARREADY;
  wire          ps7_i_M_AXI_GP1_AWREADY;
  wire          ps7_i_M_AXI_GP1_BVALID;
  wire          ps7_i_M_AXI_GP1_RLAST;
  wire          ps7_i_M_AXI_GP1_RVALID;
  wire          ps7_i_M_AXI_GP1_WREADY;
  wire [11:0]   ps7_i_M_AXI_GP1_BID;
  wire [11:0]   ps7_i_M_AXI_GP1_RID;
  wire [1:0]    ps7_i_M_AXI_GP1_BRESP;
  wire [1:0]    ps7_i_M_AXI_GP1_RRESP;
  wire [31:0]   ps7_i_M_AXI_GP1_RDATA;

  wire          ps7_o_TTC0_WAVE0_OUT;
  wire          ps7_o_TTC0_WAVE1_OUT;
  wire          ps7_o_TTC0_WAVE2_OUT;

  wire [1:0]    ps7_o_USB0_PORT_INDCTL;
  wire          ps7_o_USB0_VBUS_PWRSELECT;
  wire          ps7_o_FCLK_CLK0;
  wire          ps7_o_FCLK_RESET0_N;
  // }}} ps7 wires
  // {{{ ps7 tieoffs
  assign {
    ps7_i_M_AXI_GP0_ARREADY,
    ps7_i_M_AXI_GP0_AWREADY,
    ps7_i_M_AXI_GP0_BVALID,
    ps7_i_M_AXI_GP0_RLAST,
    ps7_i_M_AXI_GP0_RVALID,
    ps7_i_M_AXI_GP0_WREADY,
    ps7_i_M_AXI_GP0_BID,
    ps7_i_M_AXI_GP0_RID,
    ps7_i_M_AXI_GP0_BRESP,
    ps7_i_M_AXI_GP0_RRESP,
    ps7_i_M_AXI_GP0_RDATA
  } = '0;
  assign {
    ps7_i_M_AXI_GP1_ARREADY,
    ps7_i_M_AXI_GP1_AWREADY,
    ps7_i_M_AXI_GP1_BVALID,
    ps7_i_M_AXI_GP1_RLAST,
    ps7_i_M_AXI_GP1_RVALID,
    ps7_i_M_AXI_GP1_WREADY,
    ps7_i_M_AXI_GP1_BID,
    ps7_i_M_AXI_GP1_RID,
    ps7_i_M_AXI_GP1_BRESP,
    ps7_i_M_AXI_GP1_RRESP,
    ps7_i_M_AXI_GP1_RDATA
  } = '0;
  // }}} ps7 tieoffs
  ps7_ip ps7_u ( // {{{
    .M_AXI_GP0_ARVALID  (ps7_o_M_AXI_GP0_ARVALID),
    .M_AXI_GP0_AWVALID  (ps7_o_M_AXI_GP0_AWVALID),
    .M_AXI_GP0_BREADY   (ps7_o_M_AXI_GP0_BREADY),
    .M_AXI_GP0_RREADY   (ps7_o_M_AXI_GP0_RREADY),
    .M_AXI_GP0_WLAST    (ps7_o_M_AXI_GP0_WLAST),
    .M_AXI_GP0_WVALID   (ps7_o_M_AXI_GP0_WVALID),
    .M_AXI_GP0_ARID     (ps7_o_M_AXI_GP0_ARID),
    .M_AXI_GP0_AWID     (ps7_o_M_AXI_GP0_AWID),
    .M_AXI_GP0_WID      (ps7_o_M_AXI_GP0_WID),
    .M_AXI_GP0_ARBURST  (ps7_o_M_AXI_GP0_ARBURST),
    .M_AXI_GP0_ARLOCK   (ps7_o_M_AXI_GP0_ARLOCK),
    .M_AXI_GP0_ARSIZE   (ps7_o_M_AXI_GP0_ARSIZE),
    .M_AXI_GP0_AWBURST  (ps7_o_M_AXI_GP0_AWBURST),
    .M_AXI_GP0_AWLOCK   (ps7_o_M_AXI_GP0_AWLOCK),
    .M_AXI_GP0_AWSIZE   (ps7_o_M_AXI_GP0_AWSIZE),
    .M_AXI_GP0_ARPROT   (ps7_o_M_AXI_GP0_ARPROT),
    .M_AXI_GP0_AWPROT   (ps7_o_M_AXI_GP0_AWPROT),
    .M_AXI_GP0_ARADDR   (ps7_o_M_AXI_GP0_ARADDR),
    .M_AXI_GP0_AWADDR   (ps7_o_M_AXI_GP0_AWADDR),
    .M_AXI_GP0_WDATA    (ps7_o_M_AXI_GP0_WDATA),
    .M_AXI_GP0_ARCACHE  (ps7_o_M_AXI_GP0_ARCACHE),
    .M_AXI_GP0_ARLEN    (ps7_o_M_AXI_GP0_ARLEN),
    .M_AXI_GP0_ARQOS    (ps7_o_M_AXI_GP0_ARQOS),
    .M_AXI_GP0_AWCACHE  (ps7_o_M_AXI_GP0_AWCACHE),
    .M_AXI_GP0_AWLEN    (ps7_o_M_AXI_GP0_AWLEN),
    .M_AXI_GP0_AWQOS    (ps7_o_M_AXI_GP0_AWQOS),
    .M_AXI_GP0_WSTRB    (ps7_o_M_AXI_GP0_WSTRB),
    .M_AXI_GP0_ACLK     (ps7_o_FCLK_CLK0),
    .M_AXI_GP0_ARREADY  (ps7_i_M_AXI_GP0_ARREADY),
    .M_AXI_GP0_AWREADY  (ps7_i_M_AXI_GP0_AWREADY),
    .M_AXI_GP0_BVALID   (ps7_i_M_AXI_GP0_BVALID),
    .M_AXI_GP0_RLAST    (ps7_i_M_AXI_GP0_RLAST),
    .M_AXI_GP0_RVALID   (ps7_i_M_AXI_GP0_RVALID),
    .M_AXI_GP0_WREADY   (ps7_i_M_AXI_GP0_WREADY),
    .M_AXI_GP0_BID      (ps7_i_M_AXI_GP0_BID),
    .M_AXI_GP0_RID      (ps7_i_M_AXI_GP0_RID),
    .M_AXI_GP0_BRESP    (ps7_i_M_AXI_GP0_BRESP),
    .M_AXI_GP0_RRESP    (ps7_i_M_AXI_GP0_RRESP),
    .M_AXI_GP0_RDATA    (ps7_i_M_AXI_GP0_RDATA),

    .M_AXI_GP1_ARVALID  (ps7_o_M_AXI_GP1_ARVALID),
    .M_AXI_GP1_AWVALID  (ps7_o_M_AXI_GP1_AWVALID),
    .M_AXI_GP1_BREADY   (ps7_o_M_AXI_GP1_BREADY),
    .M_AXI_GP1_RREADY   (ps7_o_M_AXI_GP1_RREADY),
    .M_AXI_GP1_WLAST    (ps7_o_M_AXI_GP1_WLAST),
    .M_AXI_GP1_WVALID   (ps7_o_M_AXI_GP1_WVALID),
    .M_AXI_GP1_ARID     (ps7_o_M_AXI_GP1_ARID),
    .M_AXI_GP1_AWID     (ps7_o_M_AXI_GP1_AWID),
    .M_AXI_GP1_WID      (ps7_o_M_AXI_GP1_WID),
    .M_AXI_GP1_ARBURST  (ps7_o_M_AXI_GP1_ARBURST),
    .M_AXI_GP1_ARLOCK   (ps7_o_M_AXI_GP1_ARLOCK),
    .M_AXI_GP1_ARSIZE   (ps7_o_M_AXI_GP1_ARSIZE),
    .M_AXI_GP1_AWBURST  (ps7_o_M_AXI_GP1_AWBURST),
    .M_AXI_GP1_AWLOCK   (ps7_o_M_AXI_GP1_AWLOCK),
    .M_AXI_GP1_AWSIZE   (ps7_o_M_AXI_GP1_AWSIZE),
    .M_AXI_GP1_ARPROT   (ps7_o_M_AXI_GP1_ARPROT),
    .M_AXI_GP1_AWPROT   (ps7_o_M_AXI_GP1_AWPROT),
    .M_AXI_GP1_ARADDR   (ps7_o_M_AXI_GP1_ARADDR),
    .M_AXI_GP1_AWADDR   (ps7_o_M_AXI_GP1_AWADDR),
    .M_AXI_GP1_WDATA    (ps7_o_M_AXI_GP1_WDATA),
    .M_AXI_GP1_ARCACHE  (ps7_o_M_AXI_GP1_ARCACHE),
    .M_AXI_GP1_ARLEN    (ps7_o_M_AXI_GP1_ARLEN),
    .M_AXI_GP1_ARQOS    (ps7_o_M_AXI_GP1_ARQOS),
    .M_AXI_GP1_AWCACHE  (ps7_o_M_AXI_GP1_AWCACHE),
    .M_AXI_GP1_AWLEN    (ps7_o_M_AXI_GP1_AWLEN),
    .M_AXI_GP1_AWQOS    (ps7_o_M_AXI_GP1_AWQOS),
    .M_AXI_GP1_WSTRB    (ps7_o_M_AXI_GP1_WSTRB),
    .M_AXI_GP1_ACLK     (ps7_o_FCLK_CLK0),
    .M_AXI_GP1_ARREADY  (ps7_i_M_AXI_GP1_ARREADY),
    .M_AXI_GP1_AWREADY  (ps7_i_M_AXI_GP1_AWREADY),
    .M_AXI_GP1_BVALID   (ps7_i_M_AXI_GP1_BVALID),
    .M_AXI_GP1_RLAST    (ps7_i_M_AXI_GP1_RLAST),
    .M_AXI_GP1_RVALID   (ps7_i_M_AXI_GP1_RVALID),
    .M_AXI_GP1_WREADY   (ps7_i_M_AXI_GP1_WREADY),
    .M_AXI_GP1_BID      (ps7_i_M_AXI_GP1_BID),
    .M_AXI_GP1_RID      (ps7_i_M_AXI_GP1_RID),
    .M_AXI_GP1_BRESP    (ps7_i_M_AXI_GP1_BRESP),
    .M_AXI_GP1_RRESP    (ps7_i_M_AXI_GP1_RRESP),
    .M_AXI_GP1_RDATA    (ps7_i_M_AXI_GP1_RDATA),

    .MIO                (FIXED_IO_mio[53:0]),

    .DDR_CAS_n          (DDR_cas_n),
    .DDR_CKE            (DDR_cke),
    .DDR_Clk_n          (DDR_ck_n),
    .DDR_Clk            (DDR_ck_p),
    .DDR_CS_n           (DDR_cs_n),
    .DDR_DRSTB          (DDR_reset_n),
    .DDR_ODT            (DDR_odt),
    .DDR_RAS_n          (DDR_ras_n),
    .DDR_WEB            (DDR_we_n),
    .DDR_BankAddr       (DDR_ba[2:0]),
    .DDR_Addr           (DDR_addr[14:0]),
    .DDR_VRN            (FIXED_IO_ddr_vrn),
    .DDR_VRP            (FIXED_IO_ddr_vrp),
    .DDR_DM             (DDR_dm[3:0]),
    .DDR_DQ             (DDR_dq[31:0]),
    .DDR_DQS_n          (DDR_dqs_n[3:0]),
    .DDR_DQS            (DDR_dqs_p[3:0]),

    .TTC0_WAVE0_OUT     (ps7_o_TTC0_WAVE0_OUT),
    .TTC0_WAVE1_OUT     (ps7_o_TTC0_WAVE1_OUT),
    .TTC0_WAVE2_OUT     (ps7_o_TTC0_WAVE2_OUT),

    .USB0_PORT_INDCTL   (ps7_o_USB0_PORT_INDCTL),
    .USB0_VBUS_PWRSELECT(ps7_o_USB0_VBUS_PWRSELECT),
    .USB0_VBUS_PWRFAULT (1'b0),

    .FCLK_CLK0          (ps7_o_FCLK_CLK0),
    .FCLK_RESET0_N      (ps7_o_FCLK_RESET0_N),
    .PS_SRSTB           (FIXED_IO_ps_srstb),
    .PS_CLK             (FIXED_IO_ps_clk),
    .PS_PORB            (FIXED_IO_ps_porb)
  ); // }}}

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
