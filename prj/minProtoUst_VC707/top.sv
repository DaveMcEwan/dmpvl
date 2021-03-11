
module top (
  input  SYSCLK_P, // (E19 LVDS VC707.U51.4)
  input  SYSCLK_N, // (E18 LVDS VC707.U51.5)

  // TODO: ULPI
  // FMC connector ports                    UST-PCB-004ab/c
  inout  wire FMC2_HPC_LA00_CC_P,        // ulpi_clkout
  inout  wire FMC2_HPC_LA01_CC_P,        // ulpi_d6
  inout  wire FMC2_HPC_LA01_CC_N,        // ulpi_d7
  input  wire FMC2_HPC_LA02_P,           // ulpi_nxt
  output wire FMC2_HPC_LA02_N,           // ulpi_stp
  inout  wire FMC2_HPC_LA03_P,           // ulpi_d0
  inout  wire FMC2_HPC_LA03_N,           // ulpi_d1
  inout  wire FMC2_HPC_LA04_P,           // ulpi_d2
  inout  wire FMC2_HPC_LA04_N,           // ulpi_d3
  output wire FMC2_HPC_LA05_P,           // ulpi_resetb
  inout  wire FMC2_HPC_LA09_P,           // ulpi_d4
  inout  wire FMC2_HPC_LA09_N,           // ulpi_d5
  output wire FMC2_HPC_LA10_P,           // phy_refclk
  input  wire FMC2_HPC_LA10_N,           // ulpi_dir

  // PWM
  output GPIO_LED_0, // (AM39 LVCMOS18 VC707.DS2.2)

  // SM enabled status
  output GPIO_LED_5,

  // Test button,LEDs,
  input GPIO_SW_W,
  output GPIO_LED_6,
  output GPIO_LED_7
);
wire i_pin_sysclk_p_200MHz = SYSCLK_P;
wire i_pin_sysclk_n_200MHz = SYSCLK_N;

localparam N_PROBE  = 16;
localparam N_ENGINE = 1;

// TODO: probes,
wire [N_PROBE-1:0] i_pin_probe = '0;

wire [N_ENGINE-1:0] o_pin_pwm;
assign GPIO_LED_0 = o_pin_pwm;

// TODO: PLL freq
wire clk_ulpi;
wire pllLocked;
pllUlpi u_pllUlpi (
  .i_clk_p_200MHz (i_pin_sysclk_p_200MHz),
  .i_clk_n_200MHz (i_pin_sysclk_n_200MHz),
  .o_clk_ulpi     (clk_ulpi),
  .o_locked       (pllLocked)
);

wire rst;
fpgaReset u_rst (
  .i_clk        (clk_ulpi),
  .i_pllLocked  (pllLocked),
  .o_rst        (rst)
);

// Test debouncing.
syncBit #(
  .DEBOUNCE_CYCLES (240000), // 5ms at 48MHz, TODO: what at clk_ulpi freq?
  .EDGECNTR_W (1),
  .N_SYNC     (2)
) u_btnW (
  .i_clk        (clk_ulpi),
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



wire [N_ENGINE-1:0] resultPwm;
assign o_pin_pwm = resultPwm;



wire ust_usb0_ulpi_dir_w = FMC2_HPC_LA10_N;
wire ust_usb0_ulpi_nxt_w = FMC2_HPC_LA02_P;
assign FMC2_HPC_LA02_N = ust_usb0_ulpi_stp_w;




// TODO: tristate pins
// Tie ULPI data inputs low when transmitting.
wire [7:0] ust_usb0_ulpi_data_in_w = ust_usb0_ulpi_dir_w ? '0 : {
  FMC2_HPC_LA01_CC_N,        // ulpi_d7
  FMC2_HPC_LA01_CC_P,        // ulpi_d6
  FMC2_HPC_LA09_N,           // ulpi_d5
  FMC2_HPC_LA09_P,           // ulpi_d4
  FMC2_HPC_LA04_N,           // ulpi_d3
  FMC2_HPC_LA04_P,           // ulpi_d2
  FMC2_HPC_LA03_N,           // ulpi_d1
  FMC2_HPC_LA03_P            // ulpi_d0
};

IOBUF #(
  .DRIVE        (16),
  .IBUF_LOW_PWR ("FALSE"),
  .IOSTANDARD   ("DEFAULT"),
  .SLEW         ("FAST")
) iobuf_usbp (
  .O  (ust_usb0_ulpi_data_out_w[7]),
  .I  (usbTx_p),
  .IO (FMC2_HPC_LA01_CC_N),
  .T  (!ust_usb0_ulpi_dir_w)
);

wire [7:0] ust_usb0_ulpi_data_out_w = !ust_usb0_ulpi_dir_w ? '0 : {
  FMC2_HPC_LA01_CC_N,        // ulpi_d7
  FMC2_HPC_LA01_CC_P,        // ulpi_d6
  FMC2_HPC_LA09_N,           // ulpi_d5
  FMC2_HPC_LA09_P,           // ulpi_d4
  FMC2_HPC_LA04_N,           // ulpi_d3
  FMC2_HPC_LA04_P,           // ulpi_d2
  FMC2_HPC_LA03_N,           // ulpi_d1
  FMC2_HPC_LA03_P            // ulpi_d0
};;






module ust_ss_corrdemo0_m (
  .ust_clk_udb_ip             (clk_ulpi),
  .ust_rst_udb_ip             (rst),

  .ust_clk_usb0_usb_ip        (clk_ulpi),
  .ust_rst_usb0_usb_ip        (rst),
  .ust_usb0_ulpi_dir_ip       (ust_usb0_ulpi_dir_w),
  .ust_usb0_ulpi_nxt_ip       (ust_usb0_ulpi_nxt_w),
  .ust_usb0_ulpi_stp_op       (ust_usb0_ulpi_stp_w),
  .ust_usb0_ulpi_data_in_ip   (ust_usb0_ulpi_data_in_w),
  .ust_usb0_ulpi_data_out_op  (ust_usb0_ulpi_data_in_w),
  .ust_usb0_testmode_ip       ('0),
  .ust_usb0_vbus_ip           ('0),

  .ust_me0_gpio_out_op        (), // unused
  .ust_me0_gpio_in_ip         ('0),

  .ust_clk_sm0_sts_ip         (clk_ulpi),
  .ust_sm0_sts_match_ip       (i_pin_probe),
  .ust_sm0_sts_match_valid_ip ('1),
  .ust_sm0_sts_filter_ip      ('0),
  .ust_sm0_sts_filter_valid_ip('0),
  .ust_sm0_sts_data_ip        ('0),
  .ust_sm0_sts_data_valid_ip  ('0),
  .ust_sm0_sts_accum_ip       ('0),
  .ust_sm0_correlator_pwm_op  (resultPwm),
  .ust_en_sm0_sts_op          (GPIO_LED_5), // unused
  .ust_sm0_gpio_output_op     (), // unused
  .ust_sm0_testmode_ip        ('0),
  .ust_sm0_scan_shift_ip      ('0),
  .ust_sm0_version_op         (), // unused
  .ust_sm0_instance_id_ip     ('0) // Same as TB.
);


endmodule
