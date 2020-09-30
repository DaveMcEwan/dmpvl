
`include "dff.svh"

// Detect reset being removed.
// Second flop used to avoid asserting o_wentInactive for a partial cycle.
module resetDetect (
  input wire                    i_clk,
  input wire                    i_rst,
  output wire                   o_wentInactive
);

wire notHistoryMsb;

`dff_cg_srst(reg [1:0], rstHistory, i_clk, notHistoryMsb, i_rst, 2'b00)

assign notHistoryMsb = !rstHistory_q[1];

always @* rstHistory_d = {rstHistory_q[0], 1'b1};

assign o_wentInactive = (rstHistory_q == 2'b01);

endmodule
