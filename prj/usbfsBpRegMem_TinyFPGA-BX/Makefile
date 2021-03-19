
# Dave McEwan 2020-04-20

default: lint_foss
default: default_ice40

SRC_SINGLEHIER += ../../hdl/bpRegMem.sv
SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/fpgaReset.sv
SRC_SINGLEHIER += ../../hdl/usbfsEndpCtrlSerial.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktRx.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktTx.sv

SRC_MULTIHIER += ../../hdl/usbfsEndpRx.sv
SRC_MULTIHIER += ../../hdl/usbfsEndpTx.sv
SRC_MULTIHIER += ../../hdl/usbfsSerial.sv
SRC_MULTIHIER += ../../hdl/usbfsTxn.sv
SRC_MULTIHIER += top.sv

INCDIRS = . ../../hdl

VERILATOR_SRC_EXCLUDE += top.sv
VCS_SRC_EXCLUDE       += top.sv
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

MK_WAVEDROM := ../../mk/wavedrom.mk
include $(MK_WAVEDROM)

# NOTE: bytePipe-utils and plotCsv are bundled with dmppl.
#		Setup venv for Python 3.6+ ...
#		git clone https://github.com/DaveMcEwan/dmppl.git
#		pip install -e ./dmppl
test: $(BUILD)/$(PROJ).icepack.bin
	bytePipe-utils -v --prog --bitfile $< test
	for i in $(shell seq 0 270); do \
		bytePipe-utils -v -a=1 -n=$$i -f=/dev/null get; \
		bytePipe-utils -v -a=1 -n=$$i -f=/dev/urandom put; \
	done
.PHONY: test

# Device should be programmed first.
BW_BYTES := 10000000 # 10MB
plotBandwidth:
	bytePipe-utils -v --record-time -a=1 -f=/dev/null -n=$(BW_BYTES) get
	plotCsv -v bpRecordTime.csv -o img/BytePipe_bandwidth25s_read.png \
		--baseX --mulX=0.001 \
		--product --diffX --diffY --invX \
		--xlabel="Time (us)" --xlim=0,25000000 \
		--ylabel="Rate (MB/s)" --ylim=0,0.8 \
		--marker=""
	bytePipe-utils -v --record-time -a=1 -f=/dev/urandom -n=$(BW_BYTES) put
	plotCsv -v bpRecordTime.csv -o img/BytePipe_bandwidth25s_write.png \
		--baseX --mulX=0.001 \
		--product --diffX --diffY --invX \
		--xlabel="Time (us)" --xlim=0,25000000 \
		--ylabel="Rate (MB/s)" --ylim=0,0.8 \
		--marker=""
.PHONY: plotBandwidth
