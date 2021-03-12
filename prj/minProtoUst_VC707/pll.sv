`timescale 1ps/1ps

module pll (
  input  wire i_sysclk_p_200MHz,
  input  wire i_sysclk_n_200MHz,
  output wire o_locked,
  output wire o_clk_26MHz,
  output wire o_clk_50MHz
);

// Buffer differential pair to single ended signal.
wire clk_raw200MHz;
IBUFDS u_ibufgds_sysclk (
  .I  (i_sysclk_p_200MHz),
  .IB (i_sysclk_n_200MHz),
  .O  (clk_raw200MHz)
);

// Feedback buffer.
wire clkfbout, clkfbin;
BUFG u_bufg_clkf (
  .I (clkfbout),
  .O (clkfbin)
);

wire clkout0;
wire clkout1;
wire _unused_clkout2;
wire _unused_clkout3;
wire _unused_clkout4;
wire _unused_clkout5;

wire [15:0] _unused_do;
wire        _unused_drdy;

PLLE2_ADV #(
  .CLKIN1_PERIOD      (5.000),  // 200MHz
  .DIVCLK_DIVIDE      (5),      // 200 / 8 = 25MHz
  .CLKFBOUT_MULT      (39),     // 25 * 39 = 975MHz
  .CLKFBOUT_PHASE     (0.000),
  .CLKOUT0_DIVIDE     (37.500), // 975 / 37.5 = 26MHz
  .CLKOUT0_PHASE      (0.000),
  .CLKOUT0_DUTY_CYCLE (0.500),
  .CLKOUT1_DIVIDE     (19.500), // 975 / 37.5 = 50MHz
  .CLKOUT1_PHASE      (0.000),
  .CLKOUT1_DUTY_CYCLE (0.500),
  .BANDWIDTH          ("OPTIMIZED"),
  .COMPENSATION       ("ZHOLD"),
  .STARTUP_WAIT       ("FALSE")
) u_plle2_adv (
  .CLKIN1             (clk_raw200MHz),
  .CLKIN2             (1'b0),
  .CLKINSEL           (1'b1),

  .CLKFBIN            (clkfbin),
  .CLKFBOUT           (clkfbout),

  .CLKOUT0            (clkout0),
  .CLKOUT1            (clkout1),
  .CLKOUT2            (_unused_clkout2),
  .CLKOUT3            (_unused_clkout3),
  .CLKOUT4            (_unused_clkout4),
  .CLKOUT5            (_unused_clkout5),

  .DADDR              (7'h0),
  .DCLK               (1'b0),
  .DEN                (1'b0),
  .DI                 (16'h0),
  .DO                 (_unused_do),
  .DRDY               (_unused_drdy),
  .DWE                (1'b0),

  .LOCKED             (o_locked),
  .PWRDWN             (1'b0),
  .RST                (1'b0)
);

BUFG bufg_clk_26MHz_u (
  .I(clkout0),
  .O(o_clk_26MHz)
);

BUFG bufg_clk_50MHz_u (
  .I(clkout1),
  .O(o_clk_50MHz)
);

endmodule
