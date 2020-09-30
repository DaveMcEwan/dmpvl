
TB := VGWM_usbSerialEchoer_tb

V_SRC := \
	../../verif/generateClock.sv \
	../../verif/tristateBuffer.sv \
	../../hdl/resetDetect.sv \
	../../hdl/edgeDetect.sv \
	../../hdl/fifo.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktTxMux.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktTx.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktRx.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpInArbiter.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpOutArbiter.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPeIn.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPeOut.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPe.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbCtrlSerial.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpBridge.sv \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbSerial.sv \
	../../verif/usbFullSpeedPacketSender.sv \
	../../verif/usbFullSpeedPacketReceiver.sv \
	../../verif/usbFullSpeedTransactor.sv \
	driveHost.sv \
	$(TB).sv

LINT_SRC := driveHost.sv
IVERILOG_TOP := serialEchoer_tb

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
