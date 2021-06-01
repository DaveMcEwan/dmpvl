
SRC_SINGLEHIER += ../../hdl/resetDetect.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktRx.sv
SRC_SINGLEHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktRx.sv
SRC_SINGLEHIER += ../../verif/generateClock.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketSender.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketReceiver.sv
SRC_SINGLEHIER += drivePackets.sv

YOSYS_SRC_EXCLUDE += ../../verif/generateClock.sv
YOSYS_SRC_EXCLUDE += drivePackets.sv
YOSYS_SRC_EXCLUDE += usbFullSpeedPackets_tb.sv
VERILATOR_SRC_EXCLUDE += usbFullSpeedPackets_tb.sv

default: lint_foss
default: iverilog_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)

