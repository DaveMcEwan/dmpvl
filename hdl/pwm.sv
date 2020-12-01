`include "dff.svh"

/* Pulse Width Modulator
 *
 * Two architectures:
 * 0. Comparator gives wide pulses with fixed period of 2**WIDTH cycles.
 *  - Use a wrapping free-running counter compared against i_x.
 * 1. ΔΣ (delta-sigma) gives narrow pulses with variable period.
 *  - ΔΣ is not strictly a pulse-width-modulator but more like
 *    a pulse-frequency-modulator but the application areas overlap so having
 *    one module makes more sense for synthesis experiments.
 *
 * Comparator and ΔΣ implementations have same number of dff.
 * State of all dffs is provided on outputs for either implementation.
 * Output is straight from dff for either implementation.
 *
 * Comparator architecture is suitable for something like a communications
 * application which cares about the duty cycle.
 * NOTE: In the comparator architecture if i_x is changed when (o_acc != 0) then
 * the output will glitch.
 * ΔΣ architecture is suitable for something like an LED dimmer which cares
 * about the average DC offset.
 *
 * Input i_x is assumed to be held stable for periods much greater than 2**WIDTH
 * cycles of i_clk.
*/
module pwm #(
  parameter WIDTH = 8,  // Must be 2 or more.
  parameter ARCH = 0 // 1->ΔΣ, otherwise comparator.
) (
  input  wire                         i_clk,
  input  wire                         i_rst,
  input  wire                         i_cg,

  input  wire [WIDTH-1:0]             i_x,
  output wire [WIDTH-1:0]             o_acc,
  output wire                         o_y
);

generate if (ARCH == 1) begin : b_deltaSigma

  `dff_cg_srst(reg [WIDTH:0], acc, i_clk, i_cg, i_rst, '0)
  always @* acc_d = {1'b0, acc_q[WIDTH-1:0]} + {1'b0, i_x};

  assign o_acc = acc_q[WIDTH-1:0];

  assign o_y = acc_q[WIDTH];

end : b_deltaSigma else begin : b_comparator

  `dff_upcounter(reg [WIDTH-1:0], acc, i_clk, i_cg, i_rst)

  assign o_acc = acc_q;

  `dff_cg_srst(reg, y, i_clk, i_cg, i_rst, 1'b0)
  always @* y_d = (acc_q < i_x);
  assign o_y = y_q;

end : b_comparator endgenerate

endmodule
