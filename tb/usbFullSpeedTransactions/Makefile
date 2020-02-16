
TB := usbFullSpeedTransactions_tb

V_SRC := \
	../../hdl/resetDetect.v \
	../../verif/generateClock.v \
	../../verif/tristateBuffer.v \
	../../verif/usbFullSpeedPacketSender.v \
	../../verif/usbFullSpeedPacketReceiver.v \
	../../verif/usbFullSpeedTransactor.v \
	driveEndpointRx.v \
	driveEndpointTx.v \
	driveTransactions.v \
	$(TB).v

LINT_SRC := \
	driveEndpointRx.v \
	driveEndpointTx.v \
	driveTransactions.v

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
