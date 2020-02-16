
TB := VGWM_usbSerialEchoer_tb

V_SRC := \
	../../verif/generateClock.v \
	../../verif/tristateBuffer.v \
	../../hdl/resetDetect.v \
	../../hdl/edgeDetect.v \
	../../hdl/fifo.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktTxMux.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktTx.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktRx.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpInArbiter.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpOutArbiter.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPeIn.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPeOut.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPe.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbCtrlSerial.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpBridge.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbSerial.v \
	../../verif/usbFullSpeedPacketSender.v \
	../../verif/usbFullSpeedPacketReceiver.v \
	../../verif/usbFullSpeedTransactor.v \
	driveHost.v \
	$(TB).v

LINT_SRC := driveHost.v
IVERILOG_TOP := serialEchoer_tb

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
