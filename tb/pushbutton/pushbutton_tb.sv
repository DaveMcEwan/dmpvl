`include "asrt.svh"
`include "dff.svh"

/** pushbutton_tb.sv - Testbench for pushbutton
 * Instance name should be u_pushbutton_<debounceCycles>
 * Connecting wires should be <instance>_<port>
 */
module pushbutton_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire           i_clk,
  input  wire           i_cg,
  input  wire           i_rst,

  output wire           common_i_button,

  output wire           pushbutton_7_o_debounced,
  output wire           pushbutton_7_o_toggle,

  output wire           pushbutton_8_o_debounced,
  output wire           pushbutton_8_o_toggle,

  output wire           pushbutton_9_o_debounced,
  output wire           pushbutton_9_o_toggle
`endif
);

localparam WIDTH = 8;

// {{{ clock,clockgate,reset,dump

wire clk;
reg cg;
reg rst;

generateClock u_clk (
`ifdef VERILATOR // V_erilator must drive its own root clock
  .i_rootClk        (i_clk),
`endif
  .o_clk            (clk),
  .i_periodHi       (8'd0),
  .i_periodLo       (8'd0),
  .i_jitterControl  (8'd0)
);

`dff_nocg_norst(reg [31:0], nCycles, clk)
initial nCycles_q = '0;
always @*
  nCycles_d = nCycles_q + 'd1;

`ifdef VERILATOR // V_erilator tb drives its own clockgate,reset
always @* cg = i_cg;
always @* rst = i_rst;
`else
initial cg = 1'b1;
//always @(posedge clk) cg = ($urandom_range(9, 0) != 0); // TODO: Dynamic cg.

initial rst = 1'b1;
always @*
  if (nCycles_q > 20)
    rst = 1'b0;
  else
    rst = 1'b1;

initial begin
  $dumpfile("build/pushbutton_tb.iverilog.vcd");
  $dumpvars(0, pushbutton_tb);
end

// Finish sim after an upper limit on the number of clock cycles.
always @* if (nCycles_q > `N_CYCLES) $finish;
`endif

// }}} clock,clockgate,reset,dump

// PWM i_button with sweeping control simulates noisy button with pulses at all
// possible numbers of cycles.
// Over 2000 cycles this looks like:
//  1. Start not pressed
//  2. Noisy press
//  3. Noisy unpress
//  4. Noisy press
wire [4:0] _unused_pwm_o_acc;
pwm #(
  .WIDTH  (5),
  .ARCH   (0)
) u_pwm (
  .i_clk    (clk),
  .i_rst    (rst),
  .i_cg     (cg),

  .i_x      (nCycles_q[9:5]),
  .o_acc    (_unused_pwm_o_acc),
  .o_y      (common_i_button)
);


pushbutton #(
  .DEBOUNCE_CYCLES (7)
) u_pushbutton_7 (
  .i_clk      (clk),
  .i_cg       (cg),
  .i_rst      (rst),

  .i_button     (common_i_button),

  .o_debounced  (pushbutton_7_o_debounced),
  .o_toggle     (pushbutton_7_o_toggle)
);

pushbutton #(
  .DEBOUNCE_CYCLES (8)
) u_pushbutton_8 (
  .i_clk      (clk),
  .i_cg       (cg),
  .i_rst      (rst),

  .i_button     (common_i_button),

  .o_debounced  (pushbutton_8_o_debounced),
  .o_toggle     (pushbutton_8_o_toggle)
);

pushbutton #(
  .DEBOUNCE_CYCLES (9)
) u_pushbutton_9 (
  .i_clk      (clk),
  .i_cg       (cg),
  .i_rst      (rst),

  .i_button     (common_i_button),

  .o_debounced  (pushbutton_9_o_debounced),
  .o_toggle     (pushbutton_9_o_toggle)
);

endmodule

