
dmpvl - Dave McEwan's Personal Verilog Library
==============================================

Verilog/SystemVerilog projects.

  - hdl - HDL (Hardware Description Language) code which may be shared between
    design projects.
  - prj - A concrete realisation of code on a specific platform.
    May be a specific type of simulation, FPGA, or (wishfully!) ASIC.
    Each of these has some practical usecase.
  - tb - Testbenches for verifying modules by simulation.
    These don't really have any practical usecase other than verification.
  - verif - Components which may be shared between verification tasks.

FOSS tools are preferred.

  - iverilog - Traditional event based simulator.
  - verilator - Cycle accurate simulator.
  - yosys - Synthesis.
  - arachne-pnr - First-generation place-and-route for Lattice ice40 FPGAs.
  - nextpnr-ice40 - Second-generation place-and-route for Lattice ice40 FPGAs.
  - tinyprog - Bootloader interface utility for TinyFPGA series of boards.
  - icestorm - Collection of utilities for Lattice ice40 FPGAs.
  - gtkwave - Value Change Dump (VCD) waveform viewer.
    The config file here `.gtkwaverc` may be symlink/copied to `$HOME` or
    appropriate working directories.

TODO: More writeup
TODO: Writeup each project.
TODO: Writeup each testbench.
