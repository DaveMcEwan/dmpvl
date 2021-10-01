/** foo_tb
 */
module foo_tb (
`ifdef VERILATOR
  input  wire           i_clk,
  input  wire           i_rst
`endif
);

initial begin
  $display("Hello World!");
end

endmodule
