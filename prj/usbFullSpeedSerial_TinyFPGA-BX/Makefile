
# Dave McEwan 2020-01-21

default: lint_foss
default: default_ice40

SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/fpgaReset.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketReceiver.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedPacketSender.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedEndpointSender.sv
SRC_SINGLEHIER += ../../verif/usbFullSpeedControlSerial.sv

SRC_MULTIHIER += ../../verif/usbFullSpeedTransactor.sv
SRC_MULTIHIER += ../../verif/usbFullSpeedEndpointReceiver.sv
SRC_MULTIHIER += ../../verif/usbFullSpeedSerial.sv
SRC_MULTIHIER += top.sv

SRC_COMBINED := $(SRC_SINGLEHIER) $(SRC_MULTIHIER)

INCDIRS = . ../../hdl ../../verif

VERILATOR_SRC ?= $(subst top.sv,,$(SRC_COMBINED))
MK_LINT := ../../mk/lint.mk
include $(MK_LINT)

MK_PREPROC := ../../mk/preproc.mk
include $(MK_PREPROC)

YOSYS_SRC := $(SRC_SINGLEHIER) $(SRC_MULTIHIER) $(BUILD)/pll48.sv
#PNR_SEED ?= 1
MK_ICE40 := ../../mk/ice40.mk
include $(MK_ICE40)

MULTIPNR_ARACHNE := 1
MK_MULTIPNR := ../../mk/multipnr_ice40.mk
include $(MK_MULTIPNR)

MK_CLEAN := ../../mk/clean.mk
include $(MK_CLEAN)
