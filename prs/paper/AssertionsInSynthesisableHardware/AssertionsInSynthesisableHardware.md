Assertions In Synthesizable Hardware
====================================

- Synthesisable Properties for Designers
  - Properties vs wires on waveforms.
  - Less language to learn.
  - Easy for tools to prove.
  - Support for more tools.

* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *

TODO: Write abstract last.

Aim
---
This paper describes a particular style in which SoC digital designers can
write formal assertions with several benefits over a freestyle approach.
The main benefits of following this style include:

- Assertions are expressed as synthesisable logic which is fully supported by
  all tools for simulation, synthesis, linting (quality checking via static
  analysis), and formal proofs.
- Applicable to any Hardware Description Language (HDL) and straightforward
  translation between HDLs, e.g. SystemVerilog [cite IEEE1800],
  VHDL [cite IEEE1076].
- Designers do not need to use specialised sub-languages such as
  SystemVerilog Assertions (SVA), i.e. they can use the exact same subset of
  language features that they use for digital design.
- Simulation and emulation output of each assertion component can be viewed on
  a conventional waveform viewer, e.g. GTKWave [cite GTKWave], and stored in a
  conventional waveform format, e.g. Value Change Dump (VCD) [cite IEEE1364],
  thus enabling straightforward debugging.
- On FPGA/ASIC platforms, assertion outputs can be routed to pins for real-time
  checking via specialised equipment like an oscilloscope.

First, the Background section explains the motivations with descriptions of
existing styles and their limitations.
Second, the Method section explains the style's theory and gives robust
examples, before addressing the salient details.
Third, the Discussion section covers the most pertinent aspects of implementing
the method in the different environments of simulation/emulation,
formal analysis, and physical platform, i.e. FPGA or ASIC.


Background
----------
In digital SoCs, assertions are used to check that certain conditions are true,
with the implication that if the conditions are not met, then the design has
entered an unexpected or undesirable state.
In a simulation environment, immediate assertions only perform checks at
specific point in simulation time, i.e. in SystemVerilog, these are written
inside a scheduled process such as a `task` or `always` block.
This paper is about concurrent assertions which are checked at (almost) all
points in simulation time, and may be proven to always hold true (under
specific assumptions) via formal proof tools.
Concurrent assertions are futher divided into three categories:

Input assertions
: check that a design's inputs are being driven in the expected manner, and are
  written by both designers and verifiers.
  For example, a designer might expect (and check) that inputs `a` and `b` are
  driven in sequence with a minimum delay between tranitions.

Internal/Whitebox assertions
: check that a internal components are operating as intended, and are usually
  written by designers.
  For example, a designer might expect that a wire `w` only ever rises when
  a counter `c` contains a value of 5.

Output assertions
: check that a design drives its outputs according to a formal specification,
  and are usually written by verifiers.
  For example, a verifier will expect a design featuring a USB port, to conform
  to the USB specification.

In formal verification, input assertions may be converted to assumptions and
internal assertions may be discarded as they are inessential to meet the
block's specification.
A proof assistant tool will then confirm that there is no sequence of inputs
which violate the assertions, or provide a counterexample.
In simulation, all three categories are checked, typically on the rising edge
of a clock signal.

### Concurrent Assertions in SystemVerilog
- Examples with brief description of syntax.
- Brief overview of SVA.
- SystemVerilog is specified primarily as a programming language, a subset of
  which is synthesisable ... side-effects in action blocks, effects on
  multi-thread sim.
  - $display is IO.
  - Assignments update state.
  - Special strings like "Error" are not required with $error.


Method
------
- Create auxiliary logic, enabled only for test designs, but removed for
  production designs.
- Split out terms of CNF for easier debugging.
  - Multiple smaller assertions reduce need for chasing waves.

The style is first presented via an illustrative example:
```systemverilog
logic a_NAME;
always_comb a_NAME =      // Disjunction over a concatenation.
  |{i_rst                 // Don't check in reset.
  , !isInterestingCase    // Don't check in uninteresting case.
  , mustBeTrue            // Expression which must be true.
  };
assert property (@(posedge i_clk) a_NAME)
  else $error("DESCIPTION");
```

To begin, a variable is declared with the intention that it should be
continually assigned the value `1'b1`.
While in SystemVerilog one line may be saved by declaring a `wire` instead of
`logic`, i.e. `wire a_tristate = ... `, this would declare a continuous
assignment to a tri-state net instead of a procedural assignment to a variable.
A continuous assignment (which could also be specified like
`assign a_NAME = ...`), would mean that the value must be recalculated every
time the simulator needs to read the value.
In contrast, a procedural assignment (specified with the `always_comb`
keyword), means that the simulator must only calculate the value of `a_NAME`
when the `always_comb` procedure is triggered.
This distinction, as discussed in clauses 10.3 (page 234) and 10.4 (page 236)
of the LRM, can have significant performance consequences in simulation, so the
recommendation is to use `always_comb`.

A further benefit of preferring `always_comb` over `assign` is that the
`always_comb` keyword is specified to require that the left-hand side, i.e. the
`a_NAME` variable, is not driven by any other process.
This is useful as a self-checking mechanism against typographical errors, as
illustrated:
```systemverilog
wire y, z;
assign y = 1'b1;
assign y = 1'b0; // No compile error.
always_comb z = 1'b1;
always_comb z = 1'b0; // Compile error protects against typos.
```

A common prefix, `a_` is recommended for the assertion signals, simply to aid
identification and review.
For example, all assertions in a waveform viewer can be found using a regular
expression, and reviewers can be somewhat assured that these signals shouldn't
affect synthesis.
Additionally, upon examination of synthesis reports and netlists, engineers can
check that these auxiliary signals are, or aren't, present as desired.

The assertion is written with a list of all the ways in which the check is
allowed to pass.
It can be seen than this is logically equivalent to a material conditional
operation, where `a_NAME` is the implication, `mustBeTrue` is the consequent,
and the antcedent is `(!i_rst || isInterestingCase)`.
```
implication := (antecedent → consequent)
             = (¬antecedent ∨ consequent)  // Disjunctive form
             = ¬(antecedent ∧ ¬consequent) // Conjunctive form
```

As the disjunctive form is used, the illustrative example can be expanded for
assertions where any one from a range of terms can satisfy the assertion:
```systemverilog
always_comb a_disjunctiveForm =
  |{i_rst
  , !isInterestingCase
  , maybeTrue1            // In interesting cases, at least one of these
  , maybeTrueN            // maybeTrue* expressions must be true.
  };
```

The conjunctive form is a natural alternative to explore, written with a list
all of the ways in which the check should fail.
In practice this is less intuitive, more verbose, and thus more error-prone.
It may feel slightly easier to think of cases where you want to see the check
applied, but it is easy to forget important cases.
In other words, the conjunctive form is paraphrased like
"Only check in these specific cases.", whereas the disjunctive form is
paraphrased like "Always check, except for these specific cases." which is
more conservative from a verification point of view.
```systemverilog
always_comb a_conjunctiveForm =
  !( &{ !i_rst            // Don't check in reset.
      , isInterestingCase // Don't check in this uninteresting case.
      , shouldBeFalse1    // In in interesting cases, all of these
      , shouldBeFalseN    // shouldBeFalse* expressions must be false.
      } );
```

Assertions in either form can be combined into "super-assertions" and, again,
the difference between disjunctive-form and conjunctive-form assertions is
notable.
Combining disjunctive-form assertions where `1'b1` means "good" requires a
*con*junction, and conjunctive-form assertions require a *dis*junction to
combine them:
```systemverilog
always_comb a_allGood =   // Combine disjunctive-form assertions with a
  &{a_good                // conjunction over a concatenation.
  , a_green
  , a_shouldBeHigh
  };

always_comb a_anyBad =    // Combine conjunctive-form assertions with a
  |{a_bad                 // disjunction over a concatenation.
  , a_red
  , a_shouldBeLow
  };
```

A further point about using conjunctive-form assertions concerns those with
only expression to check (after discounting the uninteresting cases):
TODO
```systemverilog
always_comb a_ANNOYING =
  |{!isInterestingCase
  , x && y // Single consequent in CNF should be split into 1 assertion per
           // consequent term.
  };

always_comb a_EASIER_x =
  |{!isInterestingCase
  , x
  };

always_comb a_EASIER_y =
  |{!isInterestingCase
  , y
  };
```

```systemverilog
assert property (@(posedge i_clk) a_EXTRAHELPFUL)
  else begin
    $error("DESCIPTION");
    $info("counter=%0d", counter); // Extra helpful debug information.
  end
```


Discussion
----------
- Synthesisable Properties for FPGA Targets
  - One pin out per property.
    - `#pins = #assertions`
    - Use a downcounter FSM when glitches are so short that they're smoothed by
      pin capacitance (line of flops is the naive equivalent).
      - "all good this cycle" -> "all good for all of the previous N cycles"
      - "any bad this cycle" -> "all bad in any of the previous N cycles"
  - One pin for conjunction of all properties.
    - `#pins = 1`
    - Also use downcounter FSM to unsmooth glitches here.
    - Use double-flop resyncs when assertions come from different clock
      domains.
  - Popcnt for num fails, OnehotIdx for precise identification.
    - `#pins = 2 * clog2(#assertions)`
    - Also use double-flop resyncs here.
  - Replace popcnt with pair of anyViolation, exactlyOneViolation, OnehotIdx.
    - `#pins = 2 + clog2(#assertions)`
    - Use a single downcounter FSM for anyViolation and exactlyOneViolation.
    - OnehotIdx is tricker, but should allow to change faster than pins
      really allow.


Conclusion
----------



