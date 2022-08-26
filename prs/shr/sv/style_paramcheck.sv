/* Comparison of styles for writing checks/constraints on parameter values.
*/

module M
  #(int WIDTH = 5                   // Should be in (0, 23].
  , int DEPTH = 10                  // Should be in [MIN_DEPTH, MAX_DEPTH].
  , localparam int MIN_DEPTH = 2    // Non-overridable.
  , localparam int MAX_DEPTH = 64   // Non-overridable.
  ) ();


  /* 1. Explicit conjunction of all constraints, saying what you *do* want.
  If any constraint is violated, then an "elaboration system task" forces a
  compiler to stop after elaboration (before simulation) and emit a message.
  See IEEE1800-2017 Clause 20.11 (page 606) for details about elaboration
  system tasks.
  - pro: Simple, neat, readable, extensible.
  - pro: Single name "PARAMCHECK_ALLGOOD" can be common across all modules.
  - pro: Special name "PARAMCHECK_ALLGOOD" can be detected by AST analysis
    for things like documentation.
    AST analysis with a constant resolver can detect if constraints are
    violated by checking value of the specially named localparam.
    The set of constraint expressions can be extracted from the conjoined
    comma-separated list.
  - verdict: Preferred style, but see also style 7.
  */
  localparam bit PARAMCHECK_ALLGOOD =
    &{(0 < WIDTH)
    , (WIDTH < 22)
    , (MIN_DEPTH <= DEPTH)
    , (DEPTH <= MAX_DEPTH)
    };
  if (!PARAMCHECK_ALLGOOD) begin: l_paramcheck_allgood
    $error("Parameter constraint violation.");
    $info("WIDTH=%0d%", WIDTH);
    $info("DEPTH=%0d%", DEPTH);
  end: l_paramcheck_allgood


  /* 2. Explicit disjunction of all constraints, saying what you *don't* want.
  - pro: Same set of pros as explicit conjunction.
  - con: Saying what you don't want is often less intuitive than saying what
    you do want.
  - verdict: Use when it's easier to say what you *don't* want.
  */
  localparam bit PARAMCHECK_ANYBAD =
    |{(0 >= WIDTH)
    , (WIDTH >= 22)
    , (MIN_DEPTH > DEPTH)
    , (DEPTH > MAX_DEPTH)
    };
  if (PARAMCHECK_ANYBAD) begin: l_paramcheck_anybad
    $error("Parameter constraint violation.");
    $info("WIDTH=%0d%", WIDTH);
    $info("DEPTH=%0d%", DEPTH);
  end: l_paramcheck_anybad


  /* 3. Implicit conjunction of all constraints.
  - con: Without an intermediate localparam, AST analysis for extracting the
  set of constraints and detecting mis-configuration is more complex.
  - con: Too much punctuation in the `if` condition is difficult to read.
  - verdict: Don't use.
  */
  if (!&{ (0 < WIDTH)
        , (WIDTH < 22)
        , (MIN_DEPTH <= DEPTH)
        , (DEPTH <= MAX_DEPTH)
        }) begin: l_paramcheck_nolocalparam
    $error("Parameter constraint violation.");
    $info("WIDTH=%0d%", WIDTH);
    $info("DEPTH=%0d%", DEPTH);
  end: l_paramcheck_nolocalparam


  /* 4. Parameters checked individually with intermediate localparams.
  Possible naming convention: PARAMCHECK_<constraintType>_<parameterName>
  - con: Rigorous coding habits are required to ensure that all intermediate
  localparams are checked with matching elaboration system tasks.
  - con: Too verbose and susceptible to easy to make and miss mistakes.
  - con: It is unclear whether the intermediate constants are in positive
  form (saying what you want) or negative form (saying what you don't want).
  - verdict: Don't use.
  */
  localparam bit PARAMCHECK_INTMIN_WIDTH = (0 < WIDTH); // positive form
  if (!PARAMCHECK_INTMIN_WIDTH) $error("WIDTH=%0d is too small.", WIDTH);

  localparam bit PARAMCHECK_INTMAX_WIDTH = (WIDTH >= 22); // negative form
  if (PARAMCHECK_INTMAX_WIDTH) $error("WIDTH=%0d is too large.", WIDTH);


  /* 5. Parameters checked individually without intermediate localparams.
  - con: All cons of other implicit-constant styles.
  - con: Less punctation makes it tempting to use the (less intuitive) negative
  form, so easily becomes difficult for readers.
  - verdict: Don't use.
  */
  if (!(WIDTH < 22)) $error("WIDTH=%0d is too large.", WIDTH); // positive form
  if (WIDTH >= 22) $error("WIDTH=%0d is too large.", WIDTH); // negative form


  /* 6. Check performed via illegal index instead of $error.
  - pro: Compatible with every version of Verilog and SystemVerilog.
  - con: Looks hackish.
  - con: Error messages are implementation dependent.
  - con: Error messages may not contain useful values.
  - con: Multiple undriven wires.
  - verdict: Use only where backward compatibility is important.
  */
  wire [1:1] dummy1; // Only index 1/true is valid.
  wire paramcheck_allgood = dummy1[ // compact form
    &{(0 < WIDTH)
    , (WIDTH < 22)
    , (MIN_DEPTH <= DEPTH)
    , (DEPTH <= MAX_DEPTH)
    }];
  wire paramcheck_INTMIN_WIDTH = dummy1[0 < WIDTH]; // verbose form.

endmodule


/* 7. Place intermediate localparams in the module's parameter port list.
- pro: Constraint set sits beside the parameter it constrains.
- pro: Simple to use both positive and negative forms at once.
- verdict: Use only for simple modules without complicated array parameters.
*/
module N
  #(int WIDTH = 5                   // Should be in (0, 23].
  , int DEPTH = 10                  // Should be in [MIN_DEPTH, MAX_DEPTH].
  , localparam int MIN_DEPTH = 2    // Non-overridable.
  , localparam int MAX_DEPTH = 64   // Non-overridable.

  , localparam bit PARAMCHECK_ALLGOOD =   // Properties you do want.
      &{(0 < WIDTH)
      , (DEPTH <= MAX_DEPTH)
      }
  , localparam bit PARAMCHECK_ANYBAD =    // Properties you don't want.
      |{(WIDTH >= 22)
      , (DEPTH > MAX_DEPTH)
      }
  ) ();

  if (!PARAMCHECK_ALLGOOD || PARAMCHECK_ANYBAD) begin: l_paramcheck
    $error("Parameter constraint violation.");
    $info("WIDTH=%0d%", WIDTH);
    $info("DEPTH=%0d%", DEPTH);
  end: l_paramcheck

endmodule
