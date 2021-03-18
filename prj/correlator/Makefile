
# Dave McEwan 2020-12-14

SRC_SINGLEHIER :=
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

SRC_MULTIHIER :=
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

INCDIRS = . ../../hdl

VERILATOR_SRC ?= $(subst top.sv,,$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
VCS_SRC       ?= $(subst top.sv,,$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
MK_LINT := ../../mk/lint.mk
include $(MK_LINT)

MK_PREPROC := ../../mk/preproc.mk
include $(MK_PREPROC)

include ../common_ice40.mk

MULTIPNR_MK := ../multipnr_ice40.mk
MULTIPNR_ARACHNE := 1
include $(MULTIPNR_MK)
