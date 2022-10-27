Properties Beyond Assertions in SystemVerilog
=============================================

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
  SystemVerilog Assertions (SVA), i.e. they can use the exact subset of
  language features that they use for digital design.
- Simulation and emulation results of each assertion component can be viewed on
  a conventional waveform viewer, e.g. GTKWave [cite GTKWave], and stored in a
  conventional waveform format, e.g. Value Change Dump (VCD) [cite IEEE1364],
  thus enabling straightforward debugging.
- On FPGA/ASIC platforms, assertion results can be output on pins for real-time
  checking.

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

The style is first presented via an illustrative example.
```systemverilog
logic a_NAME;
assign a_NAME =           // Disjunctive form.
  |{i_rst                 // Don't check in reset.
  , !isInterestingCase    // Don't check in this uninteresting case.
  , maybeTrue1            // In interesting cases, at least one of these
  , maybeTrueN            // maybeTrue* expressions must be true.
  };
property p_NAME; @(posedge i_clk) a_NAME endproperty
assert property (p_NAME)
  else $error("DESCIPTION");
```

To begin, a variable is declared with the intention that it should be
continually assigned the value `1'b1`.
While in SystemVerilog one line may be saved by declaring a `wire` instead of
`logic`, i.e. `wire a_tristate = ... `, this declares a tri-state net instead
of variable.
TODO: invites typos because assign not alwayscomb.

TODO: Why assign not alwayscomb? Maybe change this.

The assertion is written with a list of all the ways in which the check is
allowed to pass.
It can be seen than this is logically equivalent to a material conditional
operation, where `a_NAME` is the implication, `mustBeTrue` is the consequent,
and the antcedent is `(!i_rst || isInterestingCase)`.

```
implication := (antecedent -> consequent)
             = (!antecedent || consequent)  // Disjunctive form
             = !(antecedent && !consequent) // Conjunctive form
```

The conjunctive form is a natural alternative, written with a list all of the
ways in which the check should fail.
In practice this is less intuitive, more verbose, and thus more error-prone.
```systemverilog
assign a_altform =        // Conjunctive form.
  !( &{ !i_rst            // Don't check in reset.
      , isInterestingCase // Don't check in this uninteresting case.
      , shouldBeFalse1    // In in interesting cases, all of these
      , shouldBeFalseN    // shouldBeFalse* expressions must be false.
      } );
```

```systemverilog
assert property (p_EXTRAHELPFUL)
  else begin
    $error("DESCIPTION");
    $info("counter=%0d", counter); // Extra helpful debug information.
  end
```

```systemverilog
assign a_ANNOYING =
  |{i_rst
  , !isInterestingCase
  , x && y // Single consequent in CNF should be split into 1 assertion per
           // consequent term.
  };

assign a_PLEASING_x =
  |{i_rst
  , !isInterestingCase
  , x
  };

assign a_PLEASING_y =
  |{i_rst
  , !isInterestingCase
  , y
  };
```


Discussion
----------
- Synthesisable Properties for FPGA Targets
  - One pin out per property.
    `#pins = #assertions`
  - One pin for conjunction of all properties.
    `#pins = 1`
  - Popcnt for num fails, OnehotIdx for precise identification.
    `#pins = 2 * clog2(#assertions)`
  - Replace popcnt with pair of anyViolation, exactlyOneViolation, OnehotIdx.
    `#pins = 2 + clog2(#assertions)`


Conclusion
----------



