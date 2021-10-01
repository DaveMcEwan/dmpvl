
dmpvl - Dave McEwan's Personal Verilog Library
==============================================

Verilog/SystemVerilog projects.

  - doc - External documentation.
  - hdl - HDL (Hardware Description Language) code shared between projects.
  - misc - Miscellaneous items related to this repository.
  - mk - A collection of makefile fragments.
  - prj - A concrete realisation of code on a specific platform.
    May be a specific type of simulation, FPGA, or (wishfully!) ASIC.
    Each of these has some practical usecase.
  - prs - Presentation material like slidesets or papers.
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

Begin work with something like:
```
sudo make -f mk/tools.mk apt_prereqs
make -f tools.mk
export PATH=$PWD/tools/bin:$PATH
```

To track the size of this repo by number of lines of code:

    wc -l `find hdl/ prj/ tb/ verif/ -type f | grep -vP '(build|svg)'`

TODO: More writeup
TODO: Writeup each project.
TODO: Writeup each testbench.
