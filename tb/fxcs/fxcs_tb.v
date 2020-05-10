/** fxcs_tb.sv - Testbench for fxcs_m
 * Instance name should be u_fxcs_<WIDTH>_[abstract]
 * Connecting wires should be <instance>_<port>
 * Purely combinatorial.
 */
module fxcs_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire [ 3:0]  fxcs_16_i_target,
  input  wire [15:0]  fxcs_16_i_vector,
  output wire [15:0]  fxcs_16_o_onehot,
  output wire [15:0]  fxcs_16_abstract_o_onehot,

  input  wire [ 3:0]  fxcs_9_i_target,
  input  wire [ 8:0]  fxcs_9_i_vector,
  output wire [ 8:0]  fxcs_9_o_onehot,
  output wire [ 8:0]  fxcs_9_abstract_o_onehot,

  input  wire [ 2:0]  fxcs_7_i_target,
  input  wire [ 6:0]  fxcs_7_i_vector,
  output wire [ 6:0]  fxcs_7_o_onehot,
  output wire [ 6:0]  fxcs_7_abstract_o_onehot
`endif
);

`ifndef VERILATOR // {{{ Non-V_erilator tb
reg  [ 3:0]  fxcs_16_i_target;
reg  [15:0]  fxcs_16_i_vector;
wire [15:0]  fxcs_16_o_onehot;
wire [15:0]  fxcs_16_abstract_o_onehot;

reg  [ 3:0]  fxcs_9_i_target;
reg  [ 8:0]  fxcs_9_i_vector;
wire [ 8:0]  fxcs_9_o_onehot;
wire [ 8:0]  fxcs_9_abstract_o_onehot;

reg  [ 2:0]  fxcs_7_i_target;
reg  [ 6:0]  fxcs_7_i_vector;
wire [ 6:0]  fxcs_7_o_onehot;
wire [ 6:0]  fxcs_7_abstract_o_onehot;

int tgt;
int vec;

task restrictInputs (
  input [31:0] i_width,
  input [ 3:0] i_target,
  input [15:0] i_vector,
  output [ 3:0] o_target,
  output [15:0] o_vector
);
  o_target = i_target % i_width;
  o_vector = i_vector & ((1 << i_width)-1);
endtask

// Drive (almost) the same {target,vector} to both DUTs.
task driveExhaustive;
  fxcs_16_i_target = '0;
  fxcs_16_i_vector = '0;
  fxcs_9_i_target = '0;
  fxcs_9_i_vector = '0;
  fxcs_7_i_target = '0;
  fxcs_7_i_vector = '0;
  #10;

  for (tgt=0; tgt < 16; tgt=tgt+1)
    for (vec=0; vec < (1 << 16); vec=vec+1) begin
      restrictInputs(16, tgt, vec, fxcs_16_i_target, fxcs_16_i_vector);
      restrictInputs(9,  tgt, vec, fxcs_9_i_target,  fxcs_9_i_vector);
      restrictInputs(7,  tgt, vec, fxcs_7_i_target,  fxcs_7_i_vector);
      #10;
    end

  // Pretty waves at end of time.
  fxcs_16_i_target = '0;
  fxcs_16_i_vector = '0;
  fxcs_9_i_target = '0;
  fxcs_9_i_vector = '0;
  fxcs_7_i_target = '0;
  fxcs_7_i_vector = '0;
  #20;
endtask

task checkAgainstModel (
  input [31:0] i_width,
  input [15:0] i_abstractModel_o_onehot,
  input [15:0] i_realModel_o_onehot
);
  if (i_abstractModel_o_onehot != i_realModel_o_onehot)
    $display("ERROR:t%0t WIDTH=%0d abstract.o_onehot=%h real.o_onehot=%h",
      $time, i_width, i_abstractModel_o_onehot, i_realModel_o_onehot);
endtask

initial begin
  $dumpfile("build/fxcs_tb.iverilog.vcd");
  $dumpvars(0, fxcs_tb);
  driveExhaustive();
  $finish;
end

// Run the checkers all the time.
always @* begin
  #1; // Allow logic to resolve before checking.
  checkAgainstModel(16, fxcs_16_abstract_o_onehot, fxcs_16_o_onehot);
  checkAgainstModel(9,  fxcs_9_abstract_o_onehot,  fxcs_9_o_onehot);
  checkAgainstModel(7,  fxcs_7_abstract_o_onehot,  fxcs_7_o_onehot);
end
`endif // }}} Non-V_erilator tb

fxcs #(
  .WIDTH          (16),
  .ABSTRACT_MODEL (0)
) u_fxcs_16 (
  .i_target   (fxcs_16_i_target),
  .i_vector   (fxcs_16_i_vector),
  .o_onehot   (fxcs_16_o_onehot)
);

fxcs #(
  .WIDTH          (16),
  .ABSTRACT_MODEL (1)
) u_fxcs_16_abstract (
  .i_target   (fxcs_16_i_target),
  .i_vector   (fxcs_16_i_vector),
  .o_onehot   (fxcs_16_abstract_o_onehot)
);

fxcs #(
  .WIDTH          (9),
  .ABSTRACT_MODEL (0)
) u_fxcs_9 (
  .i_target   (fxcs_9_i_target),
  .i_vector   (fxcs_9_i_vector),
  .o_onehot   (fxcs_9_o_onehot)
);

fxcs #(
  .WIDTH          (9),
  .ABSTRACT_MODEL (1)
) u_fxcs_9_abstract (
  .i_target   (fxcs_9_i_target),
  .i_vector   (fxcs_9_i_vector),
  .o_onehot   (fxcs_9_abstract_o_onehot)
);

fxcs #(
  .WIDTH          (7),
  .ABSTRACT_MODEL (0)
) u_fxcs_7 (
  .i_target   (fxcs_7_i_target),
  .i_vector   (fxcs_7_i_vector),
  .o_onehot   (fxcs_7_o_onehot)
);

fxcs #(
  .WIDTH          (7),
  .ABSTRACT_MODEL (1)
) u_fxcs_7_abstract (
  .i_target   (fxcs_7_i_target),
  .i_vector   (fxcs_7_i_vector),
  .o_onehot   (fxcs_7_abstract_o_onehot)
);

endmodule
