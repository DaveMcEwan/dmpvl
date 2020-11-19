`include "dff.svh"

// Debounce current state and toggle state from a physical pushbutton.
// Use deferring algorithm so changes are not reported until button has been in
// the same state for 32 (parameterizable) consecutive clock cycles.
// For reference, 5ms debounce with 48MHz clock requires DEBOUNCE_CYCLES=240000,
// and uses 22 DFF (sync[1:0], cntr[17:0], debounced, toggle).
module pushbutton #(
  parameter DEBOUNCE_CYCLES = 31, // >= 2
  parameter N_SYNC = 2            // >= 2
) (
  input  wire             i_clk,
  input  wire             i_cg,
  input  wire             i_rst,

  input  wire             i_button,
  output wire             o_debounced, // Debounced current state.
  output wire             o_toggle  // Toggle on each debounced press.
);

`dff_cg_srst(reg [N_SYNC-1:0], sync, i_clk, i_cg, i_rst, '0)
`dff_cg_srst(reg [$clog2(DEBOUNCE_CYCLES+1)-1:0], cntr, i_clk, i_cg, i_rst, '0)
`dff_cg_srst(reg, debounced, i_clk, i_cg, i_rst, 1'b0)
`dff_cg_srst(reg, toggle, i_clk, i_cg, i_rst, 1'b0)

always @* sync_d = {i_button, sync_q[N_SYNC-1:1]};

wire cntrMax = (cntr_q == DEBOUNCE_CYCLES);
wire inputChanged = sync_q[0] != debounced_q;
wire updateOutput = cntrMax && inputChanged;

always @*
  if      (sync_q[0] != sync_q[1])  cntr_d = 'd0;
  else if (inputChanged)            cntr_d = cntr_q + 'd1;
  else                              cntr_d = cntr_q;

always @* debounced_d = updateOutput ? sync_q[0] : debounced_q;
assign o_debounced = debounced_q;

always @* toggle_d = (updateOutput && sync_q[0]) ? !toggle_q : toggle_q;
assign o_toggle = toggle_q;

endmodule
