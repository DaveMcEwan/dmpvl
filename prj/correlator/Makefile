
# Dave McEwan 2020-12-14

default: lint_foss
default: default_ice40

SRC_SINGLEHIER += ../../hdl/corrCountRect.sv
SRC_SINGLEHIER += ../../hdl/dividerFsm.sv
SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/fpgaReset.sv
SRC_SINGLEHIER += ../../hdl/fxcs.sv
SRC_SINGLEHIER += ../../hdl/onehotIdx.sv
SRC_SINGLEHIER += ../../hdl/popcnt6.sv
SRC_SINGLEHIER += ../../hdl/prngXoshiro128p.sv
SRC_SINGLEHIER += ../../hdl/pwm.sv
SRC_SINGLEHIER += ../../hdl/syncBit.sv
SRC_SINGLEHIER += ../../hdl/usbfsEndpCtrlSerial.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktRx.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktTx.sv

SRC_MULTIHIER += ../../hdl/corrCountLogdrop.sv
SRC_MULTIHIER += ../../hdl/logdropWindow.sv
SRC_MULTIHIER += ../../hdl/mssbIdx.sv
SRC_MULTIHIER += ../../hdl/strobe.sv
SRC_MULTIHIER += ../../hdl/usbfsEndpRx.sv
SRC_MULTIHIER += ../../hdl/usbfsEndpTx.sv
SRC_MULTIHIER += ../../hdl/usbfsSerial.sv
SRC_MULTIHIER += ../../hdl/usbfsTxn.sv
SRC_MULTIHIER += ../../hdl/xbar.sv
SRC_MULTIHIER += correlator.sv
SRC_MULTIHIER += bpReg.sv
SRC_MULTIHIER += bpCorrelator.sv
SRC_MULTIHIER += usbfsBpCorrelator.sv
SRC_MULTIHIER += top.sv

SRC_COMBINED := $(SRC_SINGLEHIER) $(SRC_MULTIHIER)

INCDIRS = . ../../hdl

VERILATOR_SRC ?= $(subst top.sv,,$(SRC_COMBINED))
VCS_SRC       ?= $(subst top.sv,,$(SRC_COMBINED))
MK_LINT := ../../mk/lint.mk
include $(MK_LINT)

MK_PREPROC := ../../mk/preproc.mk
include $(MK_PREPROC)

YOSYS_SRC := $(SRC_SINGLEHIER) $(SRC_MULTIHIER) $(BUILD)/pll48.sv
PNR_SEED ?= 1
MK_ICE40 := ../../mk/ice40.mk
include $(MK_ICE40)

MULTIPNR_ARACHNE := 1
MK_MULTIPNR := ../../mk/multipnr_ice40.mk
include $(MK_MULTIPNR)

MK_CLEAN := ../../mk/clean.mk
include $(MK_CLEAN)
