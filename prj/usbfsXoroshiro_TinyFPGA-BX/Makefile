
# Dave McEwan 2020-05-03

SRC := \
	xoroshiro.sv \
	../../hdl/prngXoroshiro128p.sv \
	../../hdl/prngXoshiro128pp.sv \
	../../hdl/prngXoshiro128p.sv \
	../../hdl/prngXoshiro256p.sv \
	../../hdl/prngXoroshiro64s.sv \
	../../hdl/fxcs.sv \
	../../hdl/onehotIdx.sv \
	../../hdl/mssbIdx.sv \
	../../hdl/logdropWindow.sv \
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
.PHONY: test
test: $(BUILD)/$(PROJ).icepack.bin $(BUILD)/$(PROJ).icetime.rpt
	bytePipe-utils -v --bitfile $< test
	for i in $(shell seq 0 270); do \
		bytePipe-utils -v --no-prog -a=1 -n=$$i -f=/dev/null get; \
		bytePipe-utils -v --no-prog -a=1 -n=$$i -f=/dev/urandom put; \
	done

# Device should be programmed first.
DIST_BYTES := 10000000 # 10MB
$(BUILD)/samples.bin:
	bytePipe-utils -v --no-prog -a=1 -f=/dev/urandom -n=16 put
	bytePipe-utils -v --no-prog -a=1 -f=$@ -n=$(DIST_BYTES) get
plotDist: $(BUILD)/samples.bin
	plotDistBytes -o $(BUILD)/samples.dist $<
