Correlator on OpenPiton+Ariane
==============================

There are other correlator projects which create something akin to an
oscilloscope for measuring correlation rather than voltage:

- `prj/correlator` Reference design using TinyFPGA-BX (Lattice iCE40HX) which is
  the most difficult to build with regards to timing of the critical path.
  The relatively slow FPGA family (iCE40HX) is used as the reference design
  because if a SV2005/yosys/nextpnr design can be built successfully, then
  other, generally faster, FPGA families are likely to also build with plenty of
  timing slack.
- `prj/correlator_Zedboard` Simple port of the reference design to the
  Xilinx/Diligent Zedboard used to prove out the SV2005/Vivado flow both without
  and with a Xilinx XM105 daughterboard.
- `prj/correlator_VC707` Simple port of the reference design to the Xilinx
  VC707 with a XM105 daughterboard.
  This proves out the use of extUsb on 1.8V GPIO via the XM105.

This project `prj/corrOPA` integrates the correlator into the reference design
for the OpenPiton+Ariane project and replaces the physical probes with cache bus
monitors on the outputs of each tile.

Instructions
------------

1. Build an SD card image with the instructions on
  <https://github.com/PrincetonUniversity/openpiton/README.md>
2. Build a bitstream and program it into the VC707 via the USB/JTAG port
  `cd prj/corrOPA; make prog`
  The design will wait for the center pushbutton to be pressed before beginning
  the boot process.
3. Connect and monitor the USB/UART
  `sudo minicom -D /dev/ttyUSB0` for ttyUSB0..2 which are created by the
  Diligent JTAG programmer and the USB/UART port.
  These two USB connections may share a USB hub.
4. Connect the extUSB via XM105.J16.3..11 to a separate USB hub and start
  `correlator-tui`
5. Configure the correlator as desired before pressing the center pushbutton to
  begin booting Linux.
  At any point the West pushbutton may be used to select the LEDs to be operated
  by OpenPiton or the correlator.

XSelect/YSelect Map
-------------------

Table created by looking at post-processed version of
`piton/design/chip/rtl/chip.v.pyv` which is generated to
`openpiton/piton/design/chip/rtl/chip.tmp.v`.

Select  | Wire                                    | Interesting
------  | ----                                    | -----------
36      | `system.chip.tile_0_2_out_W_noc3_valid` | yes
35      | `system.chip.tile_0_2_out_W_noc2_valid` | yes
34      | `system.chip.tile_0_2_out_W_noc1_valid` | yes
33      | `system.chip.tile_0_2_out_S_noc3_valid` | -
32      | `system.chip.tile_0_2_out_S_noc2_valid` | -
31      | `system.chip.tile_0_2_out_S_noc1_valid` | -
30      | `system.chip.tile_0_2_out_E_noc3_valid` | -
29      | `system.chip.tile_0_2_out_E_noc2_valid` | -
28      | `system.chip.tile_0_2_out_E_noc1_valid` | -
27      | `system.chip.tile_0_2_out_N_noc3_valid` | -
26      | `system.chip.tile_0_2_out_N_noc2_valid` | -
25      | `system.chip.tile_0_2_out_N_noc1_valid` | -
24      | `system.chip.tile_0_1_out_W_noc3_valid` | yes
23      | `system.chip.tile_0_1_out_W_noc2_valid` | yes
22      | `system.chip.tile_0_1_out_W_noc1_valid` | yes
21      | `system.chip.tile_0_1_out_S_noc3_valid` | -
20      | `system.chip.tile_0_1_out_S_noc2_valid` | -
19      | `system.chip.tile_0_1_out_S_noc1_valid` | -
18      | `system.chip.tile_0_1_out_E_noc3_valid` | yes
17      | `system.chip.tile_0_1_out_E_noc2_valid` | yes
16      | `system.chip.tile_0_1_out_E_noc1_valid` | yes
15      | `system.chip.tile_0_1_out_N_noc3_valid` | -
14      | `system.chip.tile_0_1_out_N_noc2_valid` | -
13      | `system.chip.tile_0_1_out_N_noc1_valid` | -
12      | `system.chip.tile_0_0_out_W_noc3_valid` | yes
11      | `system.chip.tile_0_0_out_W_noc2_valid` | yes
10      | `system.chip.tile_0_0_out_W_noc1_valid` | yes
9       | `system.chip.tile_0_0_out_S_noc3_valid` | -
8       | `system.chip.tile_0_0_out_S_noc2_valid` | -
7       | `system.chip.tile_0_0_out_S_noc1_valid` | -
6       | `system.chip.tile_0_0_out_E_noc3_valid` | yes,offchip
5       | `system.chip.tile_0_0_out_E_noc2_valid` | yes,offchip
4       | `system.chip.tile_0_0_out_E_noc1_valid` | yes,offchip
3       | `system.chip.tile_0_0_out_N_noc3_valid` | -
2       | `system.chip.tile_0_0_out_N_noc2_valid` | -
1       | `system.chip.tile_0_0_out_N_noc1_valid` | -
0       | Fixed to GND/logical zero.
