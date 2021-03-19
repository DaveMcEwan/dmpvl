
# As a basic sanity check `make` should complete with no warnings or errors.
default: lint_foss

SRC_SINGLEHIER += generateClock.sv
SRC_SINGLEHIER += tristateBuffer.sv
SRC_SINGLEHIER += usbFullSpeedPacketSender.sv
SRC_SINGLEHIER += usbFullSpeedPacketReceiver.sv
SRC_SINGLEHIER += usbFullSpeedEndpointSender.sv
SRC_SINGLEHIER += usbFullSpeedControlSerial.sv

SRC_MULTIHIER += usbFullSpeedEndpointReceiver.sv
SRC_MULTIHIER += usbFullSpeedTransactor.sv
SRC_MULTIHIER += usbFullSpeedSerial.sv

INCDIRS = . ../hdl

YOSYS_SRC_EXCLUDE += generateClock.sv
YOSYS_SRC_EXCLUDE += tristateBuffer.sv
MK_LINT := ../mk/lint.mk
include $(MK_LINT)

