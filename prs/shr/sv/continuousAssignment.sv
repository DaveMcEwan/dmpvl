module continuousAssignment
  ( input  logic i_aNet // 1b 4-state net.
  , input  logic i_bNet // 1b 4-state net.
  , output logic o_cVar // 1b 4-state variable (not a net, good).

  , input  var logic i_dVar // 1b 4-state variable.
  , output var logic o_eVar // Semantically equivalent to o_cVar.

  , inout  tri logic b_fNet // 1b 4-state net.
  );

  // Multi-driven input net is valid.
  assign i_aNet = 1'b1; // This is valid ...
  assign i_aNet = 1'b0; // ... also valid. No warning required from compiler.

  // `always_comb` keyword enforces single driver.
  always_comb i_bNet = 1'b1; // Not an error *if input is undriven*.
  // always_comb i_bNet = 1'b0; // Compiler must emit an error.

  // Variable can only have a single driver.
  assign o_cVar = 1'b1;
  // assign o_cVar = 1'b0; // Compiler must emit an error.

  // Clarification that input port variables also have 0 or 1 drivers.
  // assign i_dVar = 1'b1; // Invalid, must be driven from outside `M`.

  // Tri-state nets can have multiple drivers, including bi-directional ports.
  // There is no such thing as a tri-state variable.
  assign b_fNet = 1'b1; // This is valid ...
  assign b_fNet = 1'b0; // ... also valid. No warning required from compiler.
  // `b_fNet` can also be driven from outside `M`.

endmodule
