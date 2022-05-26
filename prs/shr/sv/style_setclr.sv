/* Comparison of syntactic/semantic styles for writing a 1b FSM.
*/

module M;

  /* 1. Expression using only binary (AND, OR), and unary (NOT) operations.
  - pro: Most direct translation to gates.
  - pro: Can be used with continuous assignment, i.e. use the keyword `assign`
    instead of `always_comb`.
  - verdict: Preferred style.
  */
  always_comb d = set || (q && !clr);                           // Example 1.1
  assign d = set || (q && !clr);                                // Example 1.2

  /* 2. Expression using only ternary operations.
  - con: Less nice because literals can be easily/accidentally swapped.
  - pro: Can be used with continuous assignment, i.e. use the keyword `assign`
    instead of `always_comb`.
  - verdict: Don't use.
  */
  always_comb d = set ? 1'b1 : (clr ? 1'b0 : q);                // Example 2.1
  assign d = set ? 1'b1 : (clr ? 1'b0 : q);                     // Example 2.2

  /* 3. Conditional procedure.
  - con: Cannot be used with continuous assignment, i.e. cannot use the keyword
    `assign` instead of `always_comb`.
  - con: Less nice because literals can be easily/accidentally swapped.
  - con: Less nice because there's more noise to read.
  - verdict: Don't use.
  */
  always_comb                                                   // Example 3.1
    if      (set) d = 1'b1;
    else if (clr) d = 1'b0;
    else          d = q;


  /* 4. Case procedure.
  - pro: More explicit than if/else about priority between `set` and `clr`.
  - pro: Permits explicit values and function calls.
  - con: Cannot be used with continuous assignment, i.e. cannot use the keyword
    `assign` instead of `always_comb`.
  - con: Less nice because there's more noise to read.
  - verdict: Use where priority behaviour needs to be explicit.
  */
  always_comb                                                   // Example 4.1
    case ({set, clr})
      2'b00: d = q;
      2'b10: d = 1'b1;
      2'b01: d = 1'b0;
      default: d = 1'b1; // Alternatively, 1'b0, q, 1'bx, $warn, etc.
    endcase


  /* 5. Prioritise `clr` rather than `set`.
  In examples 1..3, when both `set` and `clr` are asserted, `set` is
  prioritised, but they can be changed to prioritise `clr`.
  */
  assign d = !clr && (set || q);                                // Example 5.1

  assign d = clr ? 1'b0 : (set ? 1'b1 : q);                     // Example 5.2

  always_comb                                                   // Example 5.3
    if      (clr) d = 1'b0;
    else if (set) d = 1'b1;
    else          d = q;

  /* 6. No change when both `set` and `clr` are asserted.
  */
  assign d = (set && !clr) || (q && (set != clr));              // Example 6.1

  assign d = (set != clr) ? set : q;                            // Example 6.2

  always_comb                                                   // Example 6.3
    if (set != clr) d = set;
    else            d = q;

  /* 7. Toggle when both `set` and `clr` are asserted.
  */
  assign d = (set && !q) || (q && !clr);                        // Example 7.1

  assign d = (set != clr) ? set : (set ? !q : q);               // Example 7.2

  always_comb                                                   // Example 7.3
    if      (set != clr) d = set;
    else if (set)        d = !q; // Equivalently, `else if (clr) d = !q;`.
    else                 d = q;

endmodule
