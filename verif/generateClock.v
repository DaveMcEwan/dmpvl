`include "dff.vh"

module generateClock (
`ifdef VERILATOR // V_erilator must drive its own root clock
  input  wire                       i_rootClk,
`endif

  // Generated clock.
  output wire                       o_clk,

  // Number of rootClk cycles-1 to stay hi/lo.
  input  wire [7:0]                 i_periodHi,
  input  wire [7:0]                 i_periodLo,

  // Random jitter control.
  // 0 --> No jitter
  // Higher number --> more jitter
  input  wire [7:0]                 i_jitterControl
);

`dff_nocg_norst(reg, leafClk, i_rootClk)
`dff_nocg_norst(reg [7:0], downCounter, i_rootClk)

`ifndef VERILATOR
reg i_rootClk = 0;
always #5 i_rootClk = ~i_rootClk;

initial leafClk_q = 0;
initial downCounter_q = 0;
`endif

reg [7:0] rndJitter;
always @ (posedge i_rootClk)
                                                /* verilator lint_off WIDTH */
  rndJitter = $random;
                                                /* verilator lint_on  WIDTH */

wire jitterThisCycle = (rndJitter < i_jitterControl);

always @*
  if (downCounter_q == '0)
    if (jitterThisCycle)
        // Delay
        downCounter_d = downCounter_q;
    else
      if (leafClk_q)
        downCounter_d = i_periodLo;
      else
        downCounter_d = i_periodHi;
  else
    downCounter_d = downCounter_q - 8'd1;

always @*
  if ((downCounter_q == '0) && !jitterThisCycle)
    leafClk_d = ~leafClk_q;
  else
    leafClk_d = leafClk_q;

assign o_clk = leafClk_q;

endmodule
