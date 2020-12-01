
TB := usbfsBpRegMem_tb

V_SRC := \
	../../hdl/resetDetect.sv \
	../../hdl/fifoW1R1.sv \
	../../verif/generateClock.sv \
	../../verif/tristateBuffer.sv \
	../../verif/usbFullSpeedPacketSender.sv \
	../../verif/usbFullSpeedPacketReceiver.sv \
	../../verif/usbFullSpeedTransactor.sv \
	../../hdl/usbfsPktRx.sv \
	../../hdl/usbfsPktTx.sv \
	../../hdl/usbfsTxn.sv \
	../../hdl/usbfsEndpRx.sv \
	../../hdl/usbfsEndpTx.sv \
	../../hdl/usbfsEndpCtrlSerial.sv \
	../../hdl/usbfsSerial.sv \
	../../hdl/bpRegMem.sv \
	driveHost.sv \
	$(TB).sv

LINT_SRC := driveHost.sv
IVERILOG_TOP := usbfsBpRegMem_tb

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

include ../common.mk
