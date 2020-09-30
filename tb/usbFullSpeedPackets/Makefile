
TB := usbFullSpeedPackets_tb

V_SRC := \
	../../hdl/resetDetect.sv \
	../../hdl/usbfsPktRx.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktRx.sv \
	../../verif/generateClock.sv \
	../../verif/usbFullSpeedPacketSender.sv \
	../../verif/usbFullSpeedPacketReceiver.sv \
	drivePackets.sv \
	$(TB).sv

LINT_SRC := drivePackets.sv

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
