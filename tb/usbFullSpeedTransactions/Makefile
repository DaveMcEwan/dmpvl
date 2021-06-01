
SRC_SINGLEHIER += ../../hdl/resetDetect.sv
SRC_SINGLEHIER += ../../verif/generateClock.sv
SRC_SINGLEHIER += ../../verif/tristateBuffer.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketSender.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketReceiver.sv
SRC_SINGLEHIER += driveEndpointRx.sv
SRC_SINGLEHIER += driveEndpointTx.sv
SRC_SINGLEHIER += driveTransactions.sv

SRC_MULTIHIER += ../../verif/usbFullSpeedTransactor.sv

YOSYS_SRC_EXCLUDE += ../../verif/generateClock.sv
YOSYS_SRC_EXCLUDE += ../../verif/tristateBuffer.sv
YOSYS_SRC_EXCLUDE += driveEndpointRx.sv
YOSYS_SRC_EXCLUDE += driveEndpointTx.sv
YOSYS_SRC_EXCLUDE += driveTransactions.sv
YOSYS_SRC_EXCLUDE += usbFullSpeedTransactions_tb.sv
VERILATOR_SRC_EXCLUDE += usbFullSpeedTransactions_tb.sv

default: lint_foss
default: iverilog_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)

