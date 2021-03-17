
module top (
  input  SYSCLK_P, // (E19 LVDS VC707.U51.4)
  input  SYSCLK_N, // (E18 LVDS VC707.U51.5)

  // TODO: ULPI, copied from examples/maia
  // FMC connector ports               UST-PCB-003a         UST-PCB-004a
  input  wire FMC2_HPC_LA00_CC_P,        // ulpi_clkout          ulpi_clkout
  output wire FMC2_HPC_LA00_CC_N,        //                      spdif_in0
  inout  wire FMC2_HPC_LA01_CC_P,        // ulpi_d6              ulpi_d6
  inout  wire FMC2_HPC_LA01_CC_N,        // ulpi_d7              ulpi_d7
  input  wire FMC2_HPC_LA02_P,           // ulpi_nxt             ulpi_nxt
  output wire FMC2_HPC_LA02_N,           // ulpi_stp             ulpi_stp
  inout  wire FMC2_HPC_LA03_P,           // ulpi_d0              ulpi_d0
  inout  wire FMC2_HPC_LA03_N,           // ulpi_d1              ulpi_d1
  inout  wire FMC2_HPC_LA04_P,           // ulpi_d2              ulpi_d2
  inout  wire FMC2_HPC_LA04_N,           // ulpi_d3              ulpi_d3
  output wire FMC2_HPC_LA05_P,           // ulpi_resetb          ulpi_resetb
  output wire FMC2_HPC_LA05_N,           //
  output wire FMC2_HPC_LA06_P,           //                      spdif_in1
  output wire FMC2_HPC_LA06_N,           //                      spdif_in2
  output wire FMC2_HPC_LA07_P,           // LED_01               spdif_out0
  output wire FMC2_HPC_LA07_N,           // LED_02               spdif_out1
(* PULLDOWN = "TRUE" *)
  input  wire FMC2_HPC_LA08_P,           // SW1
  inout  wire FMC2_HPC_LA08_N,           // SW2                  LCD_r5
  inout  wire FMC2_HPC_LA09_P,           // ulpi_d4              ulpi_d4
  inout  wire FMC2_HPC_LA09_N,           // ulpi_d5              ulpi_d5
  output wire FMC2_HPC_LA10_P,           // phy_refclk           phy_refclk
  input  wire FMC2_HPC_LA10_N,           // ulpi_dir             ulpi_dir
  output wire FMC2_HPC_LA11_P,           //
  output wire FMC2_HPC_LA11_N,           //                      LCD_de
  output wire FMC2_HPC_LA12_P,           //                      spdif_out2
  output wire FMC2_HPC_LA12_N,           //
  output wire FMC2_HPC_LA13_P,           //
  output wire FMC2_HPC_LA13_N,           //                      LCD_b4
  output wire FMC2_HPC_LA14_P,           //                      LCD_b5
  output wire FMC2_HPC_LA14_N,           //                      LCD_b2
  output wire FMC2_HPC_LA15_P,           //                      LCD_b0
  output wire FMC2_HPC_LA15_N,           //                      LCD_g5
  output wire FMC2_HPC_LA16_P,           //                      LCD_b3
  output wire FMC2_HPC_LA16_N,           //                      LCD_b1
(* PULLDOWN = "TRUE" *)
  input  wire FMC2_HPC_LA17_CC_P,        // tck1                 TCK
  output wire FMC2_HPC_LA17_CC_N,        //                      LCD_g4
(* PULLDOWN = "TRUE" *)
  inout  wire FMC2_HPC_LA18_CC_P,        // tck2                 LCD_g2
  output wire FMC2_HPC_LA18_CC_N,        //                      LCD_r4
  output wire FMC2_HPC_LA19_P,           //                      LCD_g0
  output wire FMC2_HPC_LA19_N,           //                      LCD_r2
  output wire FMC2_HPC_LA20_P,           //                      LCD_g3
  output wire FMC2_HPC_LA20_N,           //                      LCD_g1
  output wire FMC2_HPC_LA21_P,           //                      LCD_clk
  output wire FMC2_HPC_LA21_N,           //                      aud_sdout
  output wire FMC2_HPC_LA22_P,           //                      LCD_r0
  output wire FMC2_HPC_LA22_N,           //                      aud_nreset
  output wire FMC2_HPC_LA23_P,           //                      LCD_r3
  output wire FMC2_HPC_LA23_N,           //                      LCD_r1
(* PULLDOWN = "TRUE" *)
  inout  wire FMC2_HPC_LA24_P,           // RTCK1   o            TDI         i
(* PULLDOWN = "TRUE" *)
  inout  wire FMC2_HPC_LA24_N,           // TDO1    o            TMS         i
(* PULLUP = "TRUE" *)
  inout  wire FMC2_HPC_LA25_P,           // RTCK2   o            TRSTn       i
  output wire FMC2_HPC_LA25_N,           // TDO2    o            DBGACK      o
  output wire FMC2_HPC_LA26_P,           //                      aud_lrclk
(* PULLDOWN = "TRUE" *)
  input  wire FMC2_HPC_LA26_N,           //                      aud_sdin
  output wire FMC2_HPC_LA27_P,           //                      aud_mclk
  output wire FMC2_HPC_LA27_N,           //                      aud_bclk
(* PULLDOWN = "TRUE" *)
  inout  wire FMC2_HPC_LA28_P,           // DBGACK1 o            DBGRQ       i
(* PULLDOWN = "TRUE" *)
  inout  wire FMC2_HPC_LA28_N,           // DBGRQ1  i            RTCK        o
(* PULLUP = "TRUE" *)
  inout  wire FMC2_HPC_LA29_P,           // DBGACK2 o            JTAG_resetn i
(* PULLDOWN = "TRUE" *)
  inout  wire FMC2_HPC_LA29_N,           // DBGRQ2  i            TDO         o
(* PULLUP = "TRUE" *)
  input  wire FMC2_HPC_LA30_P,           // resetn1 i
(* PULLDOWN = "TRUE" *)
  input  wire FMC2_HPC_LA30_N,           // TMS1    i
(* PULLUP = "TRUE" *)
  input  wire FMC2_HPC_LA31_P,           // resetn2 i
(* PULLDOWN = "TRUE" *)
  input  wire FMC2_HPC_LA31_N,           // TMS2    i
(* PULLDOWN = "TRUE" *)
  input  wire FMC2_HPC_LA32_P,           // TDI1    i
(* PULLUP = "TRUE" *)
  input  wire FMC2_HPC_LA32_N,           // TRST1   i
(* PULLDOWN = "TRUE" *)
  input  wire FMC2_HPC_LA33_P,           // TDI2    i
(* PULLUP = "TRUE" *)
  input  wire FMC2_HPC_LA33_N,           // TRST2   i

  // PWM
  output GPIO_LED_0, // (AM39 LVCMOS18 VC707.DS2.2)

  // SM enabled status
  output GPIO_LED_1,

  // Test button,LEDs,
  input GPIO_SW_W,
  input GPIO_SW_E,
  output GPIO_LED_4,
  output GPIO_LED_5,
  output GPIO_LED_6,
  output GPIO_LED_7
);

localparam N_PROBE  = 16;
localparam N_ENGINE = 1;

// TODO: probes,
wire [N_PROBE-1:0] i_pin_probe = '0;

wire [N_ENGINE-1:0] o_pin_pwm;
assign GPIO_LED_0 = o_pin_pwm;

wire clk_26MHz;
wire clk_50MHz;
wire pllLocked;
pll u_pll (
  .i_sysclk_p_200MHz  (SYSCLK_P),
  .i_sysclk_n_200MHz  (SYSCLK_N),
  .o_clk_26MHz        (clk_26MHz),
  .o_clk_50MHz        (clk_50MHz),
  .o_locked           (pllLocked)
);

wire rst;
fpgaReset u_rst (
  .i_clk        (clk_50MHz),
  .i_pllLocked  (pllLocked),
  .o_rst        (rst)
);

// Test debouncing, and confirm that clocks are running.
syncBit #(
  .DEBOUNCE_CYCLES (250000), // 5ms at 50MHz
  .EDGECNTR_W (1),
  .N_SYNC     (2)
) u_btnE (
  .i_clk        (clk_26MHz),
  .i_cg         (1'b1),
  .i_rst        (rst),
  .i_bit        (GPIO_SW_E),

  .o_bit        (GPIO_LED_4),
  .o_edge       (),
  .o_rise       (),
  .o_fall       (),
  .o_nEdge      (),
  .o_nRise      (GPIO_LED_5),
  .o_nFall      ()
);
syncBit #(
  .DEBOUNCE_CYCLES (250000), // 5ms at 50MHz
  .EDGECNTR_W (1),
  .N_SYNC     (2)
) u_btnW (
  .i_clk        (clk_50MHz),
  .i_cg         (1'b1),
  .i_rst        (rst),
  .i_bit        (GPIO_SW_W),

  .o_bit        (GPIO_LED_6),
  .o_edge       (),
  .o_rise       (),
  .o_fall       (),
  .o_nEdge      (),
  .o_nRise      (GPIO_LED_7),
  .o_nFall      ()
);




wire        ust_usb0_ulpi_dir_w;
wire        ust_usb0_ulpi_nxt_w;
wire        ust_usb0_ulpi_stp_w;
wire [7:0]  ust_usb0_ulpi_data_in_w;
wire [7:0]  ust_usb0_ulpi_data_out_w;

// TODO: Hookup to something useful?
//// Debug clocks with oscilloscope on daughterboard LEDs.
//wire [3:0]  pcb004_card_led_w = {2'b00, clk_50MHz, clk_26MHz};
wire [3:0]  pcb004_card_led_w = 4'b0001;
wire [1:0]  pcb004_card_sw_w;
wire [4:0]  pcb004_joystick_w;
wire        clk_ulpi_raw60MHz; // Generated on external PHY.

// Keep USB PHY in reset for a bit to allow 13MHz clock to become established
// There is a gap, estimated to be less than 256*26MHz cycles, where the 13MHz
// clock is between 'definitely unstable' and 'presumed stable'.
// NOTE: Same technique as fpgaReset.
reg  [7:0] ulpi_13MHz_downcounter_q;
wire [7:0] ulpi_13MHz_downcounter_d;
wire ulpi_13MHz_presumeStable;
wire ulpi_13MHz_isUnstable = !pllLocked; // Used as reset for 8 dffs.
always @(posedge clk_26MHz or posedge ulpi_13MHz_isUnstable)
  if (ulpi_13MHz_isUnstable)          ulpi_13MHz_downcounter_q <= 8'hff;
  else if (!ulpi_13MHz_presumeStable) ulpi_13MHz_downcounter_q <= ulpi_13MHz_downcounter_d;
assign {ulpi_13MHz_presumeStable, ulpi_13MHz_downcounter_d} =
       {1'b0,                     ulpi_13MHz_downcounter_q} - 1;

ust_pcb_003_004_m #( // {{{
  .jtag_support_p(1),
  .j64_support_p(1)
) ust_pcb_003_004_u (
  // {{{ pins
  // FMC connector ports             // UST-PCB-003a         UST-PCB-004a
  .FMC_LA00_CC_P(FMC2_HPC_LA00_CC_P),// ulpi_clkout          ulpi_clkout
  .FMC_LA00_CC_N(FMC2_HPC_LA00_CC_N),//                      spdif_in0
  .FMC_LA01_CC_P(FMC2_HPC_LA01_CC_P),// ulpi_d6              ulpi_d6
  .FMC_LA01_CC_N(FMC2_HPC_LA01_CC_N),// ulpi_d7              ulpi_d7
  .FMC_LA02_P   (FMC2_HPC_LA02_P),   // ulpi_nxt             ulpi_nxt
  .FMC_LA02_N   (FMC2_HPC_LA02_N),   // ulpi_stp             ulpi_stp
  .FMC_LA03_P   (FMC2_HPC_LA03_P),   // ulpi_d0              ulpi_d0
  .FMC_LA03_N   (FMC2_HPC_LA03_N),   // ulpi_d1              ulpi_d1
  .FMC_LA04_P   (FMC2_HPC_LA04_P),   // ulpi_d2              ulpi_d2
  .FMC_LA04_N   (FMC2_HPC_LA04_N),   // ulpi_d3              ulpi_d3
  .FMC_LA05_P   (FMC2_HPC_LA05_P),   // ulpi_resetb          ulpi_resetb
  .FMC_LA05_N   (FMC2_HPC_LA05_N),
  .FMC_LA06_P   (FMC2_HPC_LA06_P),   //                      spdif_in1
  .FMC_LA06_N   (FMC2_HPC_LA06_N),   //                      spdif_in2
  .FMC_LA07_P   (FMC2_HPC_LA07_P),   // LED_01               spdif_out0
  .FMC_LA07_N   (FMC2_HPC_LA07_N),   // LED_02               spdif_out1
  .FMC_LA08_P   (FMC2_HPC_LA08_P),   // SW1
  .FMC_LA08_N   (FMC2_HPC_LA08_N),   // SW2                  LCD_r5
  .FMC_LA09_P   (FMC2_HPC_LA09_P),   // ulpi_d4              ulpi_d4
  .FMC_LA09_N   (FMC2_HPC_LA09_N),   // ulpi_d5              ulpi_d5
  .FMC_LA10_P   (FMC2_HPC_LA10_P),   // phy_refclk           phy_refclk 13MHz
  .FMC_LA10_N   (FMC2_HPC_LA10_N),   // ulpi_dir             ulpi_dir
  .FMC_LA11_P   (FMC2_HPC_LA11_P),
  .FMC_LA11_N   (FMC2_HPC_LA11_N),   //                      LCD_de
  .FMC_LA12_P   (FMC2_HPC_LA12_P),   //                      spdif_out2
  .FMC_LA12_N   (FMC2_HPC_LA12_N),
  .FMC_LA13_P   (FMC2_HPC_LA13_P),
  .FMC_LA13_N   (FMC2_HPC_LA13_N),   //                      LCD_b4
  .FMC_LA14_P   (FMC2_HPC_LA14_P),   //                      LCD_b5
  .FMC_LA14_N   (FMC2_HPC_LA14_N),   //                      LCD_b2
  .FMC_LA15_P   (FMC2_HPC_LA15_P),   //                      LCD_b0
  .FMC_LA15_N   (FMC2_HPC_LA15_N),   //                      LCD_g5
  .FMC_LA16_P   (FMC2_HPC_LA16_P),   //                      LCD_b3
  .FMC_LA16_N   (FMC2_HPC_LA16_N),   //                      LCD_b1
  .FMC_LA17_CC_P(FMC2_HPC_LA17_CC_P),// tck1                 TCK
  .FMC_LA17_CC_N(FMC2_HPC_LA17_CC_N),//                      LCD_g4
  .FMC_LA18_CC_P(FMC2_HPC_LA18_CC_P),// tck2                 LCD_g2
  .FMC_LA18_CC_N(FMC2_HPC_LA18_CC_N),//                      LCD_r4
  .FMC_LA19_P   (FMC2_HPC_LA19_P),   //                      LCD_g0
  .FMC_LA19_N   (FMC2_HPC_LA19_N),   //                      LCD_r2
  .FMC_LA20_P   (FMC2_HPC_LA20_P),   //                      LCD_g3
  .FMC_LA20_N   (FMC2_HPC_LA20_N),   //                      LCD_g1
  .FMC_LA21_P   (FMC2_HPC_LA21_P),   //                      LCD_clk
  .FMC_LA21_N   (FMC2_HPC_LA21_N),   //                      aud_sdout
  .FMC_LA22_P   (FMC2_HPC_LA22_P),   //                      LCD_r0
  .FMC_LA22_N   (FMC2_HPC_LA22_N),   //                      aud_nreset
  .FMC_LA23_P   (FMC2_HPC_LA23_P),   //                      LCD_r3
  .FMC_LA23_N   (FMC2_HPC_LA23_N),   //                      LCD_r1
  .FMC_LA24_P   (FMC2_HPC_LA24_P),   // RTCK1                TDI
  .FMC_LA24_N   (FMC2_HPC_LA24_N),   // TDO1                 TMS
  .FMC_LA25_P   (FMC2_HPC_LA25_P),   // RTCK2                TRSTn
  .FMC_LA25_N   (FMC2_HPC_LA25_N),   // TDO2                 DBGACK
  .FMC_LA26_P   (FMC2_HPC_LA26_P),   //                      aud_lrclk
  .FMC_LA26_N   (FMC2_HPC_LA26_N),   //                      aud_sdin
  .FMC_LA27_P   (FMC2_HPC_LA27_P),   //                      aud_mclk
  .FMC_LA27_N   (FMC2_HPC_LA27_N),   //                      aud_bclk
  .FMC_LA28_P   (FMC2_HPC_LA28_P),   // DBGACK1              DBGRQ
  .FMC_LA28_N   (FMC2_HPC_LA28_N),   // DBGRQ1               RTCK
  .FMC_LA29_P   (FMC2_HPC_LA29_P),   // DBGACK2              JTAG_resetn
  .FMC_LA29_N   (FMC2_HPC_LA29_N),   // DBGRQ2               TDO
  .FMC_LA30_P   (FMC2_HPC_LA30_P),   // resetn1
  .FMC_LA30_N   (FMC2_HPC_LA30_N),   // TMS1
  .FMC_LA31_P   (FMC2_HPC_LA31_P),   // resetn2
  .FMC_LA31_N   (FMC2_HPC_LA31_N),   // TMS2
  .FMC_LA32_P   (FMC2_HPC_LA32_P),   // TDI1
  .FMC_LA32_N   (FMC2_HPC_LA32_N),   // TRST1
  .FMC_LA33_P   (FMC2_HPC_LA33_P),   // TDI2
  .FMC_LA33_N   (FMC2_HPC_LA33_N),   // TRST2
  // }}} pins

  // LEDs and pushbuttons
  .card_led_ip(pcb004_card_led_w),
  .card_sw_op (pcb004_card_sw_w),
  .joystick_op (pcb004_joystick_w),

  // USB interface
  .ust_clk_phy_refclk_ip(clk_26MHz), // 26MHz reference straight from PLL
  .ulpi_raw_clk60_op    (clk_ulpi_raw60MHz), // Could put this through PLL for ss_corrdemo0.

  .ust_clk_usb_ip     (1'b0), // unused, goes nowhere
  .ulpi_phy_rst_n_ip  (ulpi_13MHz_presumeStable), // Hold low until 13MHz is stable.
  .ulpi_dir_op        (ust_usb0_ulpi_dir_w),
  .ulpi_nxt_op        (ust_usb0_ulpi_nxt_w),
  .ulpi_stp_ip        (ust_usb0_ulpi_stp_w),
  .ulpi_data_in_op    (ust_usb0_ulpi_data_in_w),
  .ulpi_data_out_ip   (ust_usb0_ulpi_data_out_w),

  .select_004_ip(1'b0), // Gaj's personal is 003a, broken one was 004c

  // {{{ Additional unused interfaces
  // J64
  .j64_tdo_op   (),
  .j64_tck_ip   ('0),
  .j64_tms_ip   ('0),
  .j64_tdi_ip   ('0),

  // Board select
  .jtag1_003_ip ('0), // If board 003 selected, set this to use JTAG port 1 (1.8V)
  .jtag_j64_ip  ('0),

  // LCD interface
  .lcd_r_ip  ('0),
  .lcd_g_ip  ('0),
  .lcd_b_ip  ('0),
  .lcd_clk_ip('0),
  .lcd_de_ip ('0),

  // JTAG interface
  .ext_tck_op   (),
  .ext_tms_op   (),
  .ext_tdi_op   (),
  .ext_tdo_ip   ('0),
  .ext_tdo_oe_ip('0),
  .ext_trst_n_op(),

  // Audio interface
  .audio_rstn_ip ('0),
  .audio_mclk_ip ('0),
  .audio_bclk_ip ('0),
  .audio_lrclk_ip('0),
  .audio_dout_ip ('0),
  .audio_din_op  (),

  .spdif_out_ip  ('0),
  .spdif_in_op   (),

  // IODELAY support
  .ust_clk_200_ip   ('0), // unused, goes nowhere
  .ust_rst_idelay_ip('0), // unused, goes nowhere

  // Debug out
  .debug_op()             // unused, Paul's bringup aid
  // }}} Additional unused interfaces
); // }}} ust_pcb_003_004_m

ust_ss_corrdemo0_m ust_ss_corrdemo0_u (
  .ust_clk_udb_ip             (clk_50MHz),
  .ust_rst_udb_ip             (rst),

  .ust_clk_usb0_usb_ip        (clk_ulpi_raw60MHz),
  .ust_rst_usb0_usb_ip        (!ulpi_13MHz_presumeStable),
  .ust_usb0_ulpi_dir_ip       (ust_usb0_ulpi_dir_w),
  .ust_usb0_ulpi_nxt_ip       (ust_usb0_ulpi_nxt_w),
  .ust_usb0_ulpi_stp_op       (ust_usb0_ulpi_stp_w),
  .ust_usb0_ulpi_data_in_ip   (ust_usb0_ulpi_data_in_w),
  .ust_usb0_ulpi_data_out_op  (ust_usb0_ulpi_data_out_w),
  .ust_usb0_testmode_ip       ('0),
  .ust_usb0_vbus_ip           ('0),

  .ust_me0_gpio_out_op        (), // unused
  .ust_me0_gpio_in_ip         ('0),

  .ust_clk_sm0_sts_ip         (clk_50MHz),
  .ust_sm0_sts_match_ip       (i_pin_probe),
  .ust_sm0_sts_match_valid_ip ('1),
  .ust_sm0_sts_filter_ip      ('0),
  .ust_sm0_sts_filter_valid_ip('0),
  .ust_sm0_sts_data_ip        ('0),
  .ust_sm0_sts_data_valid_ip  ('0),
  .ust_sm0_sts_accum_ip       ('0),
  .ust_sm0_correlator_pwm_op  (o_pin_pwm),
  .ust_en_sm0_sts_op          (GPIO_LED_1),
  .ust_sm0_gpio_output_op     (), // unused
  .ust_sm0_testmode_ip        ('0),
  .ust_sm0_scan_shift_ip      ('0),
  .ust_sm0_version_op         (), // unused
  .ust_sm0_instance_id_ip     ('0) // Same as TB.
);


endmodule
