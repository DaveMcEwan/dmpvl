
# NOTE: Expected to fail lint_foss.

SRC_SINGLEHIER += ../../hdl/edgeDetect.sv
SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/resetDetect.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktRx.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktTx.sv
SRC_SINGLEHIER += ../../hdl/usbfsEndpCtrlSerial.sv
SRC_SINGLEHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktTxMux.sv
SRC_SINGLEHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktTx.sv
SRC_SINGLEHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktRx.sv
SRC_SINGLEHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpInArbiter.sv
SRC_SINGLEHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpOutArbiter.sv
SRC_SINGLEHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPeIn.sv
SRC_SINGLEHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPeOut.sv
SRC_SINGLEHIER += ../../verif/generateClock.sv
SRC_SINGLEHIER += ../../verif/tristateBuffer.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketSender.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketReceiver.sv
SRC_SINGLEHIER += driveHost.sv

SRC_MULTIHIER += ../../hdl/usbfsTxn.sv
SRC_MULTIHIER += ../../hdl/usbfsEndpRx.sv
SRC_MULTIHIER += ../../hdl/usbfsEndpTx.sv
SRC_MULTIHIER += ../../hdl/usbfsSerial.sv
SRC_MULTIHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPe.sv
SRC_MULTIHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbCtrlSerial.sv
SRC_MULTIHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpBridge.sv
SRC_MULTIHIER += ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbSerial.sv
SRC_MULTIHIER += ../../verif/usbFullSpeedTransactor.sv

YOSYS_SRC_EXCLUDE += ../../verif/generateClock.sv
YOSYS_SRC_EXCLUDE += ../../verif/tristateBuffer.sv
YOSYS_SRC_EXCLUDE += driveHost.sv
YOSYS_SRC_EXCLUDE += VGWM_usbSerialEchoer_tb.sv
VERILATOR_SRC_EXCLUDE += VGWM_usbSerialEchoer_tb.sv

INCDIRS = . ../../hdl ../../verif ../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX

default: lint_foss
default: iverilog_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)

