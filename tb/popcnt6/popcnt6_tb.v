/** popcnt6_tb.sv - Testbench for popcnt6
 * Instance name should be u_popcnt6_[abstract]
 * Connecting wires should be <instance>_<port>
 * Purely combinatorial.
 */
module popcnt6_tb (
`ifdef VERILATOR // V_erilator testbench can only drive IO from C++.
  input  wire [5:0]         popcnt6_i_x,
  output wire [2:0]         popcnt6_o_count,
  output wire [2:0]         popcnt6_abstract_o_count
`endif
);

`ifndef VERILATOR // {{{ Non-V_erilator tb
reg  [5:0] popcnt6_i_x;
wire [2:0] popcnt6_o_count;
wire [2:0] popcnt6_abstract_o_count;

int pattern;

task restrictInputs (
  input [31:0] i_x,
  output [5:0] o_x
);
  o_x = i_x & ((1 << 6)-1);
endtask

task driveExhaustive;
  popcnt6_i_x = '0;
  #10;

  // 3x as many as required to (paranoidly) check against lurking states.
  for (pattern=0; pattern < 3*(1 << 6); pattern=pattern+1) begin
    restrictInputs(pattern, popcnt6_i_x);
    #10;
  end

  // Pretty waves at end of time.
  popcnt6_i_x = '0;
  #20;
endtask

task checkAgainstModel (
  input [2:0] i_abstractModel_o_count,
  input [2:0] i_realModel_o_count
);
  if (i_abstractModel_o_count != i_realModel_o_count)
    $display("ERROR:t%0t abstract.o_count=%h real.o_count=%h",
      $time, i_abstractModel_o_count, i_realModel_o_count);
endtask

initial begin
  $dumpfile("build/popcnt6_tb.iverilog.vcd");
  $dumpvars(0, popcnt6_tb);
  driveExhaustive();
  $finish;
end

// Run the checkers all the time.
always @* begin
  #1; // Allow logic to resolve before checking.
  checkAgainstModel(popcnt6_abstract_o_count, popcnt6_o_count);
end
`endif // }}} Non-V_erilator tb

popcnt6 #(
  .ABSTRACT_MODEL (0)
) u_popcnt6_u (
  .i_x     (popcnt6_i_x),
  .o_count (popcnt6_o_count)
);

popcnt6 #(
  .ABSTRACT_MODEL (1)
) u_popcnt6_abstract (
  .i_x     (popcnt6_i_x),
  .o_count (popcnt6_abstract_o_count)
);

endmodule

