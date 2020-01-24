/** onehotIdx_tb.sv - Testbench for onehotIdx
 * Exhaustively test all valid input combinations.
 * Instance name should be u_onehotIdx_<WIDTH>
 * Connecting wires should be <instance>_<port>
 * Purely combinatorial.
 */
module onehotIdx_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire [15:0]  onehotIdx_16_i_onehot,
  output wire [ 3:0]  onehotIdx_16_o_index,
  output wire         onehotIdx_16_o_valid,

  input  wire [ 8:0]  onehotIdx_9_i_onehot,
  output wire [ 3:0]  onehotIdx_9_o_index,
  output wire         onehotIdx_9_o_valid
`endif
);

`ifndef VERILATOR // {{{ Non-V_erilator tb
reg  [15:0]  onehotIdx_16_i_onehot;
wire [ 3:0]  onehotIdx_16_o_index;
wire         onehotIdx_16_o_valid;

reg  [ 8:0]  onehotIdx_9_i_onehot;
wire [ 3:0]  onehotIdx_9_o_index;
wire         onehotIdx_9_o_valid;

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
  onehotIdx_16_i_onehot = '0;
  onehotIdx_9_i_onehot = '0;
  #10;

  // 3x as many as required to (paranoidly) check against lurking states.
  for (i=0; i < 3*16; i=i+1) begin
    restrictInputs(16, i, onehotIdx_16_i_onehot);
    restrictInputs(9,  i, onehotIdx_9_i_onehot);
    #10;
  end

  // Pretty waves at end of time.
  onehotIdx_16_i_onehot = '0;
  onehotIdx_9_i_onehot = '0;
  #20;
endtask

task checker (
  input int     width,
  input [15:0]  i_onehot,
  input [ 3:0]  o_index,
  input         o_valid
);

  // Model behaviour assumes input is put through a find-first-set to ensure the
  // input satisfies onehot0.
  // This does not reflect reality for input vectors with multiple bits set, so
  // that behaviour is undefined and untested.
  int b;
  int model_o_index;
  bit model_o_valid;
  model_o_index = 0;
  model_o_valid = 0;
  for (b=0; b < width; b=b+1) begin
    if (i_onehot[b] && !model_o_valid) begin
      model_o_index = b;
      model_o_valid = 1;
    end
  end

  if (o_index != model_o_index)
    $display("ERROR:t%0t WIDTH=%0d i_onehot=%h model.o_index=%h o_index=%h",
      $time, width, i_onehot, model_o_index, o_index);

  if (o_valid != model_o_valid)
    $display("ERROR:t%0t WIDTH=%0d i_onehot=%h model.o_valid=%h o_valid=%h",
      $time, width, i_onehot, model_o_valid, o_valid);
endtask

initial begin
  $dumpfile("build/onehotIdx_tb.iverilog.vcd");
  $dumpvars(0, onehotIdx_tb);
  driveExhaustive();
  $finish;
end

// Run the checkers all the time.
always @* begin
  #1; // Allow logic to resolve before checking.
  checker(16, onehotIdx_16_i_onehot, onehotIdx_16_o_index, onehotIdx_16_o_valid);
  checker(9, onehotIdx_9_i_onehot, onehotIdx_9_o_index, onehotIdx_9_o_valid);
end
`endif // }}} Non-V_erilator tb

onehotIdx #(
  .WIDTH  (16)
) u_onehotIdx_16 (
  .i_onehot   (onehotIdx_16_i_onehot),
  .o_index    (onehotIdx_16_o_index),
  .o_valid    (onehotIdx_16_o_valid)
);

onehotIdx #(
  .WIDTH  (9)
) u_onehotIdx_9 (
  .i_onehot   (onehotIdx_9_i_onehot),
  .o_index    (onehotIdx_9_o_index),
  .o_valid    (onehotIdx_9_o_valid)
);

endmodule
