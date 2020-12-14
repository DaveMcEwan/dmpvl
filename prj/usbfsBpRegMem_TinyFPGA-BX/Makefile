
# Dave McEwan 2020-04-20

SRC := \
	../../hdl/bpRegMem.sv \
	../../hdl/fifoW1R1.sv \
	../../hdl/fpgaReset.sv \
	../../hdl/usbfsPktRx.sv \
	../../hdl/usbfsPktTx.sv \
	../../hdl/usbfsTxn.sv \
	../../hdl/usbfsEndpRx.sv \
	../../hdl/usbfsEndpTx.sv \
	../../hdl/usbfsEndpCtrlSerial.sv \
	../../hdl/usbfsSerial.sv \
	./build/pll48.sv \
	top.sv

include ../common_ice40.mk

MULTIPNR_MK := ../multipnr_ice40.mk
MULTIPNR_ARACHNE := 1
include $(MULTIPNR_MK)

# Setup venv for Python 3.6+ ...
# git clone https://github.com/DaveMcEwan/dmppl.git
# pip install -e ./dmppl
test: $(BUILD)/$(PROJ).icepack.bin $(BUILD)/$(PROJ).icetime.rpt
	bytePipe-utils -v --bitfile $< test
	for i in $(shell seq 0 270); do \
		bytePipe-utils -v --no-prog -a=1 -n=$$i -f=/dev/null get; \
		bytePipe-utils -v --no-prog -a=1 -n=$$i -f=/dev/urandom put; \
	done

# Device should be programmed first.
BW_BYTES := 10000000 # 10MB
plotBandwidth:
	bytePipe-utils -v --no-prog --record-time -a=1 -f=/dev/null -n=$(BW_BYTES) get
	plotCsv -v bpRecordTime.csv -o img/BytePipe_bandwidth25s_read.png \
		--baseX --mulX=0.001 \
		--product --diffX --diffY --invX \
		--xlabel="Time (us)" --xlim=0,25000000 \
		--ylabel="Rate (MB/s)" --ylim=0,0.8 \
		--marker=""
	bytePipe-utils -v --no-prog --record-time -a=1 -f=/dev/urandom -n=$(BW_BYTES) put
	plotCsv -v bpRecordTime.csv -o img/BytePipe_bandwidth25s_write.png \
		--baseX --mulX=0.001 \
		--product --diffX --diffY --invX \
		--xlabel="Time (us)" --xlim=0,25000000 \
		--ylabel="Rate (MB/s)" --ylim=0,0.8 \
		--marker=""

# Setup venv for Python 3.6+ ...
# pip install wavedrom
WAVEDROM_JSON = $(wildcard *.wavedrom.json)
WAVEDROM_SVG = $(WAVEDROM_JSON:.wavedrom.json=.wavedrom.svg)
wavedrom: $(WAVEDROM_SVG)
%.wavedrom.svg: %.wavedrom.json
	wavedrompy -i $^ -s $@

.SECONDARY:
.PHONY: test wavedrom
