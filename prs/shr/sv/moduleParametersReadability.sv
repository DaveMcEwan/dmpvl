// I intend that this parameter may be overidden with ...
module moduleParametersReadability
  #(parameter bit A = 1 // 2-state 1b
                        // ... a boolean (true or false),
                        // OR single bit integer (0 or 1).

  , parameter int B = 5 // 2-state 32b
                        // ... a *signed* integer.
                        // Do you really allow negative values?

  , parameter int unsigned C = 5  // 2-state 32b
                                  // ... an *unsigned* integer.
                                  // That's probably what you allow.

  , parameter bit [31:0] D = 5  // 2-state 32b
                                // ... an unsigned integer,
                                // OR a 32b vector of known values.

  , parameter E = 5 // 4-state 32b
                    // ... Xs and Zs. Do you really?!
  ) ();
endmodule
