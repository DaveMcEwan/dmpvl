
TB := usbFullSpeedPackets_tb

V_SRC := \
	../../hdl/resetDetect.v \
	../../hdl/usbfsPktRx.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktRx.v \
	../../verif/generateClock.v \
	../../verif/usbFullSpeedPacketSender.v \
	../../verif/usbFullSpeedPacketReceiver.v \
	drivePackets.v \
	$(TB).v

LINT_SRC := drivePackets.v

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
