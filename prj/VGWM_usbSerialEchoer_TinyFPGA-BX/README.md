
VGWM\_usbSerialEchoer
=====================

VGWM stands for the surname initials of the main authors of this design (Luke
Valenty, Lawrie Griffiths, David Williams, Dave McEwan).
This design has nearly identical goals as `prj/TODOusbFSSerial` and
`prj/usbFullSpeedSerial` in that the aim is to create a USB Full Speed serial
device.
The origins of this design are well described by David Williams on his
[repository](https://github.com/davidthings/tinyfpga_bx_usbserial).
In short, it was originally written by Luke for the TinyFPGA bootloader, then
adapted by Lawrie to make a PicoRV32 based Arduino-like board, then adapted by
David Williams to a pipeline interface.
David Williams also explored putting the design on other platforms, the Lattice
ECP5 and the Xilinx 7-Series.

My contributions to the design have been:

  1. Reduce the number of LUTs required (881 vs 1093).
  2. Increasing the probability of passing timing, see multipnr for details.
  3. Fixing the warnings produced by yosys, iverilog, and verilator.
  4. Making it simulation compatible with the `usbFullSpeed*` verification
     components and building a testbench `tb/VGWM_usbSerialEchoer`.

These improvements have mostly been in coding style, moving from very
behavioural Verilog to a much more structured style using macros to clearly
describe what is intended.
Other tweaks have included reducing the packet size parameters, reducing net
widths, adding the alternative mode to appear as a generic serial device
(`/dev/ttyUSB0` instead of `/dev/ttyACM0`).

The structure and usage of this project are the same as
`prj/usbFullSpeedSerial`, so see that for more details.
