/** mssbIdx_tb.sv - Testbench for mssbIdx
 * Exhaustively test all valid input combinations.
 * Instance name should be u_mssbIdx_<WIDTH>
 * Connecting wires should be <instance>_<port>
 * Purely combinatorial.
 */
module mssbIdx_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire [15:0]  mssbIdx_16_i_vector,
  output wire [ 3:0]  mssbIdx_16_o_index,
  output wire         mssbIdx_16_o_valid,

  input  wire [ 8:0]  mssbIdx_9_i_vector,
  output wire [ 3:0]  mssbIdx_9_o_index,
  output wire         mssbIdx_9_o_valid,

  input  wire [ 6:0]  mssbIdx_7_i_vector,
  output wire [ 2:0]  mssbIdx_7_o_index,
  output wire         mssbIdx_7_o_valid
`endif
);

`ifndef VERILATOR // {{{ Non-V_erilator tb
reg  [15:0]  mssbIdx_16_i_vector;
wire [ 3:0]  mssbIdx_16_o_index;
wire         mssbIdx_16_o_valid;

reg  [ 8:0]  mssbIdx_9_i_vector;
wire [ 3:0]  mssbIdx_9_o_index;
wire         mssbIdx_9_o_valid;

reg  [ 6:0]  mssbIdx_7_i_vector;
wire [ 2:0]  mssbIdx_7_o_index;
wire         mssbIdx_7_o_valid;

int i;

task restrictInputs (
  input [31:0] width,
  input [31:0] bitIdx,
  output [15:0] onehot
);
  onehot = (1 << (bitIdx % width));
endtask

// Drive (almost) the same pattern to both DUTs.
task driveExhaustive;
  mssbIdx_16_i_vector = '0;
  mssbIdx_9_i_vector = '0;
  mssbIdx_7_i_vector = '0;
  #10;

  // TODO

  // Pretty waves at end of time.
  mssbIdx_16_i_vector = '0;
  mssbIdx_9_i_vector = '0;
  mssbIdx_7_i_vector = '0;
  #20;
endtask

task checker (
  input int     width,
  input [15:0]  i_vector,
  input [ 3:0]  o_index,
  input         o_valid
);

  int model_o_index;
  bit model_o_valid;
  // TODO model

  if (o_index != model_o_index)
    $display("ERROR:t%0t WIDTH=%0d i_vector=%h model.o_index=%h o_index=%h",
      $time, width, i_vector, model_o_index, o_index);

  if (o_valid != model_o_valid)
    $display("ERROR:t%0t WIDTH=%0d i_vector=%h model.o_valid=%h o_valid=%h",
      $time, width, i_vector, model_o_valid, o_valid);
endtask

initial begin
  $dumpfile("build/mssbIdx_tb.iverilog.vcd");
  $dumpvars(0, mssbIdx_tb);
  driveExhaustive();
  $finish;
end

// Run the checkers all the time.
always @* begin
  #1; // Allow logic to resolve before checking.
  checker(16, mssbIdx_16_i_vector, mssbIdx_16_o_index, mssbIdx_16_o_valid);
  checker(9, mssbIdx_9_i_vector, mssbIdx_9_o_index, mssbIdx_9_o_valid);
  checker(7, mssbIdx_7_i_vector, mssbIdx_7_o_index, mssbIdx_7_o_valid);
end
`endif // }}} Non-V_erilator tb

mssbIdx #(
  .WIDTH  (16)
) u_mssbIdx_16 (
  .i_vector   (mssbIdx_16_i_vector),
  .o_index    (mssbIdx_16_o_index),
  .o_valid    (mssbIdx_16_o_valid)
);

mssbIdx #(
  .WIDTH  (9)
) u_mssbIdx_9 (
  .i_vector   (mssbIdx_9_i_vector),
  .o_index    (mssbIdx_9_o_index),
  .o_valid    (mssbIdx_9_o_valid)
);

mssbIdx #(
  .WIDTH  (7)
) u_mssbIdx_7 (
  .i_vector   (mssbIdx_7_i_vector),
  .o_index    (mssbIdx_7_o_index),
  .o_valid    (mssbIdx_7_o_valid)
);

endmodule
