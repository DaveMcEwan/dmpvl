
# Dave McEwan 2020-05-03

default: lint_foss
default: default_ice40

SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/fpgaReset.sv
SRC_SINGLEHIER += ../../hdl/onehotIdx.sv
SRC_SINGLEHIER += ../../hdl/prngXoroshiro128p.sv
SRC_SINGLEHIER += ../../hdl/prngXoshiro128pp.sv
SRC_SINGLEHIER += ../../hdl/prngXoshiro128p.sv
SRC_SINGLEHIER += ../../hdl/prngXoshiro256p.sv
SRC_SINGLEHIER += ../../hdl/prngXoroshiro64s.sv
SRC_SINGLEHIER += ../../hdl/usbfsEndpCtrlSerial.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktRx.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktTx.sv

SRC_MULTIHIER += ../../hdl/fxcs.sv
SRC_MULTIHIER += ../../hdl/logdropWindow.sv
SRC_MULTIHIER += ../../hdl/mssbIdx.sv
SRC_MULTIHIER += ../../hdl/usbfsEndpRx.sv
SRC_MULTIHIER += ../../hdl/usbfsEndpTx.sv
SRC_MULTIHIER += ../../hdl/usbfsSerial.sv
SRC_MULTIHIER += ../../hdl/usbfsTxn.sv
SRC_MULTIHIER += xoroshiro.sv
SRC_MULTIHIER += top.sv

SRC_COMBINED := $(SRC_SINGLEHIER) $(SRC_MULTIHIER)

INCDIRS = . ../../hdl

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

# Setup venv for Python 3.6+ ...
# git clone https://github.com/DaveMcEwan/dmppl.git
# pip install -e ./dmppl
.PHONY: test
test: $(BUILD)/$(PROJ).icepack.bin
	bytePipe-utils -v --prog --bitfile $< test
	for i in $(shell seq 0 270); do \
		bytePipe-utils -v -a=1 -n=$$i -f=/dev/null get; \
		bytePipe-utils -v -a=1 -n=$$i -f=/dev/urandom put; \
	done

# Device should be programmed first.
DIST_BYTES := 10000000 # 10MB
$(BUILD)/samples.bin:
	bytePipe-utils -v -a=1 -f=/dev/urandom -n=16 put
	bytePipe-utils -v -a=1 -f=$@ -n=$(DIST_BYTES) get
plotDist: $(BUILD)/samples.bin
	plotDistBytes -o $(BUILD)/samples.dist $<
