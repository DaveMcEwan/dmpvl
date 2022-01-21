// I intend that this parameter may be overidden with ...
module example #(
  // ... a boolean (true or false),
  // OR single bit integer (0 or 1).
  bit A = 1, // 2-state 1b

  // ... a *signed* integer.
  // Do you really allow negative values?
  int B = 5, // 2-state 32b

  // ... an *unsigned* integer.
  // That's probably what you allow.
  int unsigned C = 5, // 2-state 32b

  // ... an unsigned integer,
  // OR a 32b vector of known values.
  bit [31:0] D = 5, // 2-state 32b

  // ... Xs and Zs. Do you really?!
  E = 5, // 4-state 32b

  // The parameter keyword is optional.
  parameter bit F = 0
) ();
endmodule
