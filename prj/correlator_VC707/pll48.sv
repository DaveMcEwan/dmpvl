`timescale 1ps/1ps

module pll48 (
  input  wire i_clk_p_200MHz,
  input  wire i_clk_n_200MHz,
  output wire o_locked,
  output wire o_clk_48MHz
);

// Buffer differential pair to single ended signal.
wire clk_200MHz;
IBUFDS clkin1_ibufgds (
  .I  (i_clk_p_200MHz),
  .IB (i_clk_n_200MHz),
  .O  (clk_200MHz)
);


// Feedback buffer.
wire clkfbout;
wire clkfbin;
BUFG u_bufg_clkf (
  .I (clkfbout),
  .O (clkfbin)
);

wire clkout0;
wire _unused_clkout1;
wire _unused_clkout2;
wire _unused_clkout3;
wire _unused_clkout4;
wire _unused_clkout5;

wire [15:0] _unused_do;
wire        _unused_drdy;

PLLE2_ADV #(
  .BANDWIDTH          ("OPTIMIZED"),
  .COMPENSATION       ("ZHOLD"),
  .STARTUP_WAIT       ("FALSE"),
  .DIVCLK_DIVIDE      (5),
  .CLKFBOUT_MULT      (24),
  .CLKFBOUT_PHASE     (0.000),
  .CLKOUT0_DIVIDE     (20),
  .CLKOUT0_PHASE      (0.000),
  .CLKOUT0_DUTY_CYCLE (0.500),
  .CLKIN1_PERIOD      (5.000))
u_plle2_adv (
  .CLKIN1             (clk_200MHz),
  .CLKIN2             (1'b0),
  .CLKINSEL           (1'b1),

  .CLKFBIN            (clkfbin),
  .CLKFBOUT           (clkfbout),

  .CLKOUT0            (clkout0),
  .CLKOUT1            (_unused_clkout1),
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

BUFG u_bufg_clkout0 (
  .I (clkout0),
  .O (o_clk_48MHz)
);

endmodule
