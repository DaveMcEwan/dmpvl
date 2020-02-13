`include "asrt.vh"
`include "dff.vh"

/** dividerFsm_tb.sv - Testbench for dividerFsm
 * Instance name should be u_dividerFsm_<width>_[abstract]
 * Connecting wires should be <instance>_<port>
 */
module dividerFsm_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire           i_clk,
  input  wire           i_cg,
  input  wire           i_rst,

  input  wire           common_i_begin,
  input  wire [7:0]     common_i_dividend,
  input  wire [7:0]     common_i_divisor,

  output wire           dividerFsm_8_o_busy,
  output wire [7:0]     dividerFsm_8_o_quotient,
  output wire [7:0]     dividerFsm_8_o_remainder,

  output wire           dividerFsm_8_abstract_o_busy,
  output wire [7:0]     dividerFsm_8_abstract_o_quotient,
  output wire [7:0]     dividerFsm_8_abstract_o_remainder
`endif
);

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
always @(posedge clk) cg = ($urandom_range(9, 0) != 0);

initial rst = 1'b1;
always @*
  if (nCycles_q > 20)
    rst = 1'b0;
  else
    rst = 1'b1;

initial begin
  $dumpfile("build/dividerFsm_tb.iverilog.vcd");
  $dumpvars(0, dividerFsm_tb);
end

// Finish sim after an upper limit on the number of clock cycles.
always @* if (nCycles_q > 100000) $finish;
`endif

// }}} clock,clockgate,reset,dump

`ifndef VERILATOR // {{{ Non-V_erilator tb
reg           common_i_begin;
reg [7:0]     common_i_dividend;
reg [7:0]     common_i_divisor;

wire           dividerFsm_8_o_busy;
wire [7:0]     dividerFsm_8_o_quotient;
wire [7:0]     dividerFsm_8_o_remainder;

wire           dividerFsm_8_abstract_o_busy;
wire [7:0]     dividerFsm_8_abstract_o_quotient;
wire [7:0]     dividerFsm_8_abstract_o_remainder;

always @(posedge clk)
  if (dividerFsm_8_o_busy) begin
    common_i_begin <= 1'b0;
  end else begin
    common_i_begin <= ($urandom_range(9, 0) == 0);
    common_i_dividend <= $urandom_range(255, 0);
    common_i_divisor <= $urandom_range(255, 0);
  end

`endif // }}} Non-V_erilator tb

dividerFsm #(
  .WIDTH          (8),
  .ABSTRACT_MODEL (0)
) u_dividerFsm_8 (
  .i_clk      (clk),
  .i_cg       (cg),
  .i_rst      (rst),

  .i_begin    (common_i_begin),
  .i_dividend (common_i_dividend),
  .i_divisor  (common_i_divisor),

  .o_busy     (dividerFsm_8_o_busy),
  .o_quotient (dividerFsm_8_o_quotient),
  .o_remainder(dividerFsm_8_o_remainder)
);

dividerFsm #(
  .WIDTH          (8),
  .ABSTRACT_MODEL (1)
) u_dividerFsm_8_abstract (
  .i_clk      (clk),
  .i_cg       (cg),
  .i_rst      (rst),

  .i_begin    (common_i_begin),
  .i_dividend (common_i_dividend),
  .i_divisor  (common_i_divisor),

  .o_busy     (dividerFsm_8_abstract_o_busy),
  .o_quotient (dividerFsm_8_abstract_o_quotient),
  .o_remainder(dividerFsm_8_abstract_o_remainder)
);

wire busy8 = dividerFsm_8_o_busy;
`asrt(quotient, clk, !rst && !busy8, dividerFsm_8_o_quotient == dividerFsm_8_abstract_o_quotient)
`asrt(remainder, clk, !rst && !busy8, dividerFsm_8_o_remainder == dividerFsm_8_abstract_o_remainder)

endmodule

