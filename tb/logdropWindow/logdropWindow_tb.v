/** WIP/UNTESTED
logdropWindow_tb.sv - Testbench for logdropWindow_m
 * Purely combinatorial.
 */
module logdropWindow_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire [ 5:0]  logdropWindow_A_i_t,
  input  wire [ 7:0]  logdropWindow_A_i_x,
  output wire [ 7:0]  logdropWindow_A_o_y,
  output wire [ 7:0]  logdropWindow_A_abstract_o_y,

  input  wire [ 3:0]  logdropWindow_B_i_t,
  input  wire [ 4:0]  logdropWindow_B_i_x,
  output wire [ 4:0]  logdropWindow_B_o_y,
  output wire [ 4:0]  logdropWindow_B_abstract_o_y
`endif
);

`ifndef VERILATOR // {{{ Non-V_erilator tb
reg  [ 5:0]  logdropWindow_A_i_t;
reg  [ 7:0]  logdropWindow_A_i_x;
wire [ 7:0]  logdropWindow_A_o_y;
wire [ 7:0]  logdropWindow_A_abstract_o_y;

reg  [ 3:0]  logdropWindow_B_i_t;
reg  [ 4:0]  logdropWindow_B_i_x;
wire [ 4:0]  logdropWindow_B_o_y;
wire [ 4:0]  logdropWindow_B_abstract_o_y;

int t;
int x;

task restrictInputs (
  input [31:0] i_DATA_W,
  input [ 3:0] i_t,
  input [15:0] i_x,
  output [ 3:0] o_t,
  output [15:0] o_x
);
  o_t = i_t % i_DATA_W;
  o_x = i_x & ((1 << i_DATA_W)-1);
endtask

// Drive (almost) the same {target,vector} to both DUTs.
task driveExhaustive;
  logdropWindow_A_i_t = '0;
  logdropWindow_A_i_x = '0;
  logdropWindow_B_i_t = '0;
  logdropWindow_B_i_x = '0;
  #10;

  for (t=0; t < 150; t=t+1)
    for (x=0; x < (1 << 16); x=x+1) begin
      restrictInputs(8, t, x, logdropWindow_A_i_t, logdropWindow_A_i_x);
      restrictInputs(5, t, x, logdropWindow_B_i_t, logdropWindow_B_i_x);
      #10;
    end

  // Pretty waves at end of time.
  logdropWindow_A_i_t = '0;
  logdropWindow_A_i_x = '0;
  logdropWindow_B_i_t = '0;
  logdropWindow_B_i_x = '0;
  #20;
endtask

task checkAgainstModel (
  input [31:0] i_DATA_W,
  input [15:0] i_abstractModel_o_y,
  input [15:0] i_realModel_o_y
);
  if (i_abstractModel_o_y != i_realModel_o_y)
    $display("ERROR:t%0t DATA_W=%0d abstract.o_y=%h real.o_y=%h",
      $time, i_width, i_abstractModel_o_y, i_realModel_o_y);
endtask

initial begin
  $dumpfile("build/logdropWindow_tb.iverilog.vcd");
  $dumpvars(0, logdropWindow_tb);
  driveExhaustive();
  $finish;
end

// Run the checkers all the time.
always @* begin
  #1; // Allow logic to resolve before checking.
  checkAgainstModel(8, logdropWindow_A_abstract_o_y, logdropWindow_A_o_y);
  checkAgainstModel(5, logdropWindow_B_abstract_o_y, logdropWindow_B_o_y);
end
`endif // }}} Non-V_erilator tb

logdropWindow #(
  .DATA_W         (8),
  .WINLEN         (64),
  .ABSTRACT_MODEL (0)
) logdropWindow_A_u (
  .i_t  (logdropWindow_A_i_t),
  .i_x  (logdropWindow_A_i_x),
  .o_y  (logdropWindow_A_o_y)
);

logdropWindow #(
  .DATA_W         (8),
  .WINLEN         (64),
  .ABSTRACT_MODEL (1)
) logdropWindow_A_abstract_u (
  .i_t  (logdropWindow_A_i_t),
  .i_x  (logdropWindow_A_i_x),
  .o_y  (logdropWindow_A_abstract_o_y)
);

logdropWindow #(
  .DATA_W         (5),
  .WINLEN         (16),
  .ABSTRACT_MODEL (0)
) logdropWindow_B_u (
  .i_t  (logdropWindow_B_i_t),
  .i_x  (logdropWindow_B_i_x),
  .o_y  (logdropWindow_B_o_y)
);

logdropWindow #(
  .DATA_W         (5),
  .WINLEN         (16),
  .ABSTRACT_MODEL (1)
) logdropWindow_B_abstract_u (
  .i_t  (logdropWindow_B_i_t),
  .i_x  (logdropWindow_B_i_x),
  .o_y  (logdropWindow_B_abstract_o_y)
);

endmodule
