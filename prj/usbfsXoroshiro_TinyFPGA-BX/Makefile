
# Dave McEwan 2020-05-03

# TinyFPGA-BX
DEVICE ?= lp8k
PACKAGE ?= cm81
PCF ?= pins.pcf

PROJ := top
BUILD := ./build

SRC := \
	xoroshiro.v \
	../../hdl/prngXoroshiro128p.v \
	../../hdl/prngXoshiro128pp.v \
	../../hdl/prngXoshiro128p.v \
	../../hdl/prngXoshiro256p.v \
	../../hdl/prngXoroshiro64s.v \
	../../hdl/fxcs.v \
	../../hdl/onehotIdx.v \
	../../hdl/mssbIdx.v \
	../../hdl/logdropWindow.v \
	../../hdl/fifo.v \
	../../hdl/fpgaReset.v \
	../../hdl/usbfsPktRx.v \
	../../hdl/usbfsPktTx.v \
	../../hdl/usbfsTxn.v \
	../../hdl/usbfsEndpRx.v \
	../../hdl/usbfsEndpTx.v \
	../../hdl/usbfsEndpCtrlSerial.v \
	../../hdl/usbfsSerial.v \
	$(BUILD)/pll48.v \
	$(PROJ).v

# Target fMax, not the PLL frequency.
# The design components are tied to a PLL frequency of 48MHz.
TGT_FMAX = 48

# NOTE: Finding a good seed requires some trials and won't necessarily be good
# for other setups (minor code changes, tool versions, host OS version, etc).
# Use multipnr to find a suitable seed.
PNR_SEED ?= 5

default: $(BUILD)/$(PROJ).icetime.rpt $(BUILD)/$(PROJ).icepack.bin

synth: $(BUILD)/$(PROJ).yosys.json
pnr: $(BUILD)/$(PROJ).nextpnr.asc
pack: $(BUILD)/$(PROJ).icepack.bin
rpt: $(BUILD)/$(PROJ).icetime.rpt
all: synth pnr pack rpt test wavedrom

$(BUILD)/pll48.v:
	mkdir -p $(BUILD)
	icepll \
		-q \
		-i 16 \
		-o 48 \
		-n pll48 \
		-m -f $@

# JSON netlist format - specific to yosys/nextpnr.
# BLIF netlist is usable with other tools, like Vivado.
%.yosys.json: $(SRC)
	yosys -q \
		-l $*.yosys.log \
		-p 'read_verilog -sv -I../../hdl/ $^' \
		-p 'synth_ice40 -top $(PROJ) -blif $*.yosys.blif -json $@'

%.nextpnr.asc: $(PCF) %.yosys.json
	nextpnr-ice40 -q \
		--$(DEVICE) --package $(PACKAGE) --pcf $(PCF) \
		-l $*.nextpnr.log \
		--freq $(TGT_FMAX) \
		--seed $(PNR_SEED) \
		--opt-timing \
		--json $*.yosys.json \
		--write $*.nextpnr.json \
		--asc $@

gui: $(PCF) $(BUILD)/$(PROJ).yosys.json
	nextpnr-ice40 --gui \
		--$(DEVICE) --package $(PACKAGE) --pcf $(PCF) \
		-l $(BUILD)/$(PROJ).nextpnr.log \
		--freq $(TGT_FMAX) \
		--seed $(PNR_SEED) \
		--opt-timing \
		--json $(BUILD)/$(PROJ).yosys.json \
		--asc $(BUILD)/$(PROJ).asc

%.icepack.bin: %.nextpnr.asc
	icepack $< $@

%.icetime.rpt: %.nextpnr.asc
	icetime -d $(DEVICE) -mtr $@ $<

prog: $(BUILD)/$(PROJ).icepack.bin
	tinyprog -p $<

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
DIST_BYTES := 10000000 # 10MB
$(BUILD)/samples.bin:
	bytePipe-utils -v --no-prog -a=1 -f=/dev/urandom -n=16 put
	bytePipe-utils -v --no-prog -a=1 -f=$@ -n=$(DIST_BYTES) get
plotDist: $(BUILD)/samples.bin
	plotDistBytes -o $(BUILD)/samples.dist $<

clean:
	rm -rf build
	rm -rf multipnr
	rm -f *.wavedrom.svg

.SECONDARY:
.PHONY: default all synth pnr pack rpt prog test clean gui
