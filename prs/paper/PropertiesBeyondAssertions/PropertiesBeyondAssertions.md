TODO Properties Beyond Assertions in SystemVerilog
=============================================

- Tutorial paper on the use of design assertions.

- Split out terms of CNF for easier debugging.
  - Multiple smaller assertions reduce need for chasing waves.

- Monadic code in action blocks, effects on multi-thread sim.
  - $display is IO.
  - Assignments update state.
  - Special strings like "Error" are not required with $error.

- Synthesisable Properties for Designers
  - Properties vs wires on waveforms.
  - Less language to learn.
  - Easy for tools to prove.
  - Support for more tools.

- Synthesisable Properties for FPGA Targets
  - One pin out per property.
    `#pins = #assertions`
  - One pin for conjunction of all properties.
    `#pins = 1`
  - Popcnt for num fails, OnehotIdx for precise identification.
    `#pins = 2 * clog2(#assertions)`
  - Replate popcnt with pair of anyViolation, exactlyOneViolation, OnehotIdx.
    `#pins = 2 + clog2(#assertions)`

