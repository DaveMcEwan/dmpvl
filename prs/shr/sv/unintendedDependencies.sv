module example ();
  logic a, b, y, z;
  // Execute expensive() when y or z change.
  always_comb begin
    a = expensive(y);
    b = z;
  end
  /* This is kinder to the simulator.
  always_comb a = expensive();
  always_comb b = z;
  */

  logic [4:0] c, x;
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

  /*
  When exection within begin/end has side effects,
  sim/synth mis-match may occur.
  Clause 13.4.2:
  Functions defined within a module, interface, program, or
  package default to being static, with all declared items
  being statically allocated. These items shall be shared
  across all uses of the function executing concurrently.
  */
  always_comb for (int i=0; i < 5; i++) begin
    d[i] = sideEffects(x[i]);
  end
  generate for (genvar i=0; i < 5; i++) begin
    always_comb e[i] = sideEffects(x[i]);
  end endgenerate
endmodule
