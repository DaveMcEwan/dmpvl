module example ();
  // Execute expensive() when y or z change.
  always_comb begin
    a = expensive(y);
    b = z;
  end
  /* This is kinder to the simulator.
  always_comb a = expensive();
  always_comb b = z;
  */

  // Update *every* element of c when
  // *any* element of x changes.
  always_comb for (int i=0; i < 5; i++) begin
    c[i] = expensive(x[i]);
  end
  /* This is kinder to the simulator.
  generate for (genvar i=0; i < 5; i++) begin
    always_comb c[i] = expensive(x[i]);
  end endgenerate
  */
endmodule
