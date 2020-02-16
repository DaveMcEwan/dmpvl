
TB := usbfsSerial_tb

V_SRC := \
	../../hdl/resetDetect.v \
	../../hdl/fifo.v \
	../../verif/generateClock.v \
	../../verif/tristateBuffer.v \
	../../verif/usbFullSpeedPacketSender.v \
	../../verif/usbFullSpeedPacketReceiver.v \
	../../verif/usbFullSpeedTransactor.v \
	../../hdl/usbfsPktRx.v \
	../../hdl/usbfsPktTx.v \
	../../hdl/usbfsTxn.v \
	../../hdl/usbfsEndpRx.v \
	../../hdl/usbfsEndpTx.v \
	../../hdl/usbfsEndpCtrlSerial.v \
	../../hdl/usbfsSerial.v \
	driveHost.v \
	$(TB).v

LINT_SRC := driveHost.v
IVERILOG_TOP := serialEchoer_tb

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
