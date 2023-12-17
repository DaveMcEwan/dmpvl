module nestedCondition ();
  logic clk, a, b, c, y, z, foo;

  // No else clauses.
  // Intended or accidental?
  always_ff @(posedge clk)
    if (a)
      if (b)
        if (c)
          z <= foo;

  // Fully explicit, and easier to relate to synthesized hardware.
  always_ff @(posedge clk)
    y <= (a && b && c) ? foo : y;

  // Logically equivalent, but easier for synth tools.
  always_ff @(posedge clk)
    if (a)
      y <= (b && c) ? foo : y;

endmodule
