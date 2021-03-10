
# Dave McEwan 2020-12-14

SRC := \
	../../hdl/fpgaReset.sv \
	../../hdl/usbfsPktRx.sv \
	../../hdl/usbfsPktTx.sv \
	../../hdl/usbfsTxn.sv \
	../../hdl/usbfsEndpRx.sv \
	../../hdl/usbfsEndpTx.sv \
	../../hdl/usbfsEndpCtrlSerial.sv \
	../../hdl/usbfsSerial.sv \
	../../hdl/fifoW1R1.sv \
	../../hdl/fxcs.sv \
	../../hdl/logdropWindow.sv \
	../../hdl/mssbIdx.sv \
	../../hdl/onehotIdx.sv \
	../../hdl/prngXoshiro128p.sv \
	../../hdl/strobe.sv \
	../../hdl/pwm.sv \
	../../hdl/dividerFsm.sv \
	../../hdl/corrCountRect.sv \
	../../hdl/corrCountLogdrop.sv \
	../../hdl/xbar.sv \
	correlator.sv \
	bpReg.sv \
	bpCorrelator.sv \
	usbfsBpCorrelator.sv \
	./build/pll48.sv \
	top.sv

LINT_VERILATOR_SRC := \
	correlator.sv \
	bpReg.sv \
	bpCorrelator.sv \
	usbfsBpCorrelator.sv

LINT_IVERILOG_SRC := \
	$(LINT_VERILATOR_SRC) \
	top.sv

LINT_YOSYS_SRC := \
	$(LINT_VERILATOR_SRC) \
	top.sv

PREPROC_SRC := \
	$(LINT_VERILATOR_SRC)

include ../common_ice40.mk

MULTIPNR_MK := ../multipnr_ice40.mk
MULTIPNR_ARACHNE := 1
include $(MULTIPNR_MK)
