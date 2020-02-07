
WIP/unfinished RISC-V Simple Machine (RSM)
==========================================

This project is intended to compare different coding styles and languages by
implementing the same thing, designed with a diagram.
A small CPU (RISC-V) is chosen as it is a reasonably complicated machine which
should demonstrate all of the most common features of hardware design languages
(HDL)s.

The following features of HDLs are explicitly exercised:

3. Hierarchy.
2. IO pin names.
1. Combinatorial logic.
4. D-type flip flop (FF) in different configurations.
  1. With clockgate, without reset. (data flow)
  2. With clockgate, with reset. (control flow)
  3. Without clockgate, with reset. (control flow)

The following requirements are used to create the design:

1. Minimum set of RV32I ISA features from 20190608-Base-Ratified, running and
   passing standard RISC-V tests.
2. Single clock domain.
3. Single synchronous active-low reset.
4. No combinatorial loops, or other weird asynchronous logic.
5. Memory access (external to CPU) is assumed to not reply same-cycle.
6. IO is simply clock, reset, and AXI interfaces for instructions and data.
7. All outputs must come straight from flops with no logic to give
   simple output timing constraints.
8. All inputs must go straight from flops, not driving any logic, to give
   simple input timing constraints.
9. At least one implementation, assumed to be faithful to the diagram, should
   be formally verified.
   Other implementation netlists can be checked with a logical equivalence
   check.
   Intend to use yosys-sbt.

The design intended to be educational and easy to visualize in a diagram.
It is not optimized for small size, fast clockrate, low power usage, or high
performance on any particular FPGA or ASIC process.
However, it is intended to be pretty small, run at a pretty high clockrate, be
pretty frugal with power (both dynamic and static), and have easily
predictable performance.

In order to demonstrate that the design is feasible it should be implemented on
physical FPGA targets.
When building for physical targets additional IO may be used in order to take
external inputs or show the runtime status of demonstration software.
These may be implemented as simple CSR registers.


Getting Started
---------------

1. Make sure the environment variable `$(RISCV)` is set to point to your
    riscv-tools installation.
   <https://github.com/riscv/riscv-tools>
2. Ensure Icarus and Verilator are installed.
   <http://iverilog.icarus.com/>
   <https://www.veripool.org/wiki/verilator>
3. Build all hardware models, compile `sw/hello/main.c` and run with Icarus and
   Verilator by running `make` from this directory.


NOTES
=====

TODO
----

1. `rsm_alu.svg`
2. `rsm_lsu.svg`
3. `rsm_csr.svg`
4. `rsm.svg`
5. Other implementations.


ISA
---

Supporting misaligned memory accesses makes the LSU much more complicated,
with many more flops.
However, this is necessary to pass the tests.

`FENCE.I` from `Zifencei` doesn't really do anything in an implementation this
simple, other than increase `$PC` and any instruction counters.

Counters from `Zicsr` are not necessary  but may be included anyway.


Source Language
---------------

Most languages will compile to some subset of a primitive version of Verilog.
More modern languages give you lots of convenient features but you absolutely
need to be able to speak Verilog, to be able to actually understand how to fix
the timing critical parts of a design.
This selection of HDLs have been chosen based on a mixture of personal
experience and what was "hot" at ORConf18.

1. System Verilog 2005
2. System Verilog 2012 *TODO*
3. Migen *TODO*
4. Clash *TODO*
3. MyHDL *TODO*
5. Chisel3 *TODO*
6. SpinalHDL *TODO*
7. VHDL *TODO*

Intermediate Language

1. none, straight to netlist
2. Verilog
3. VHDL

Synthesis Tool

1. Yosys *TODO*
2. Vivado *TODO*
3. Quartus *TODO*
4. Diamond/SynplifyPro *TODO*

Place and Route Tool

1. nextpnr *TODO*
2. arachnepnr *TODO?*
3. Vivado *TODO*
4. Quartus *TODO*
5. Diamond/iCEcube2 *TODO*

Target FPGA

1. ICE40LP8K *TODO*
2. Xilinx something... *TODO*


Source Structure: Flat vs Hierarchical
--------------------------------------

Hierarchy forces you to think about the interfaces between parts of the system
This is a useful layer of abstraction above the details of each block.

Hierarchy requires quite a lot of plumbing in Verilog which is boring and error
prone.
Hungarian notation (`i_*`, `o_*`, `*_d`, `*_q`) makes reading this a bit easier.

Blocks in hierarchy could be swapped out for equivalents with the same
interfaces but are optimized for a particular target.
