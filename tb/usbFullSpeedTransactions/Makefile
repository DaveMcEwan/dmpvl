
TB := usbFullSpeedTransactions_tb

V_SRC := \
	../../hdl/resetDetect.sv \
	../../verif/generateClock.sv \
	../../verif/tristateBuffer.sv \
	../../verif/usbFullSpeedPacketSender.sv \
	../../verif/usbFullSpeedPacketReceiver.sv \
	../../verif/usbFullSpeedTransactor.sv \
	driveEndpointRx.sv \
	driveEndpointTx.sv \
	driveTransactions.sv \
	$(TB).sv

LINT_SRC := \
	driveEndpointRx.sv \
	driveEndpointTx.sv \
	driveTransactions.sv

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
