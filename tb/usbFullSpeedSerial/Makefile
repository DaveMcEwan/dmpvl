
# NOTE: Expected to fail.

SRC_SINGLEHIER += ../../hdl/resetDetect.sv
SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../verif/generateClock.sv
SRC_SINGLEHIER += ../../verif/tristateBuffer.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketSender.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketReceiver.sv
SRC_SINGLEHIER += driveHost.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedControlSerial.sv

SRC_MULTIHIER += ../../verif/usbFullSpeedTransactor.sv
SRC_MULTIHIER += ../../verif/usbFullSpeedEndpointSender.sv
SRC_MULTIHIER += ../../verif/usbFullSpeedEndpointReceiver.sv
SRC_MULTIHIER += ../../verif/usbFullSpeedSerial.sv

YOSYS_SRC_EXCLUDE += ../../verif/generateClock.sv
YOSYS_SRC_EXCLUDE += driveHost.sv
YOSYS_SRC_EXCLUDE += usbFullSpeedSerial_tb.sv
VERILATOR_SRC_EXCLUDE += usbFullSpeedSerial_tb.sv

IVERILOG_TB_TOP := serialEchoer_tb

default: lint_foss
default: iverilog_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)

