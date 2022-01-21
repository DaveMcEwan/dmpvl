module example (
  input  logic a, // 1b 4-state net (not a variable).
  input  logic b, // 1b 4-state net (not a variable).
  output logic c, // 1b 4-state variable (not a net, good).

  input  var logic d, // 1b 4-state variable (not a net, good).
  output var logic e  // 1b 4-state variable (not a net, good).
);
  assign a = 1; // Multi-driven input is valid.
  assign a = 0; // Still valid. No warning required from compiler.

  // New keyword enforces single driver.
  always_comb b = 1; // Not an error *if input is undriven*.
  // always_comb b = 0; // Compiler must emit error.

  // Variable can only have a single driver.
  assign c = 1;
  // assign c = 0; // Compiler must emit error.
endmodule
