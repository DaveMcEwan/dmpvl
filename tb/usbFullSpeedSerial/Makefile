
TB := usbFullSpeedSerial_tb

V_SRC := \
	../../hdl/resetDetect.sv \
	../../verif/generateClock.sv \
	../../verif/tristateBuffer.sv \
	../../hdl/fifo.sv \
	../../verif/usbFullSpeedPacketSender.sv \
	../../verif/usbFullSpeedPacketReceiver.sv \
	../../verif/usbFullSpeedTransactor.sv \
	../../verif/usbFullSpeedControlSerial.sv \
	../../verif/usbFullSpeedEndpointSender.sv \
	../../verif/usbFullSpeedEndpointReceiver.sv \
	../../verif/usbFullSpeedSerial.sv \
	driveHost.sv \
	$(TB).sv

LINT_SRC := driveHost.sv
IVERILOG_TOP := serialEchoer_tb

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
