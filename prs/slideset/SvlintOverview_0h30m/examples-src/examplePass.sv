module M;
  always_ff @(posedge clk) z <= z - 1;
endmodule
