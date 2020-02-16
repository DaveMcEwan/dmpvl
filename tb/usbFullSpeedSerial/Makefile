
TB := usbFullSpeedSerial_tb

V_SRC := \
	../../hdl/resetDetect.v \
	../../verif/generateClock.v \
	../../verif/tristateBuffer.v \
	../../hdl/fifo.v \
	../../verif/usbFullSpeedPacketSender.v \
	../../verif/usbFullSpeedPacketReceiver.v \
	../../verif/usbFullSpeedTransactor.v \
	../../verif/usbFullSpeedControlSerial.v \
	../../verif/usbFullSpeedEndpointSender.v \
	../../verif/usbFullSpeedEndpointReceiver.v \
	../../verif/usbFullSpeedSerial.v \
	driveHost.v \
	$(TB).v

LINT_SRC := driveHost.v
IVERILOG_TOP := serialEchoer_tb

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
