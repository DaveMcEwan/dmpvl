
# Dave McEwan 2020-04-20

# TinyFPGA-BX
DEVICE ?= lp8k
PACKAGE ?= cm81
PCF ?= pins.pcf

PROJ := top
BUILD := ./build

SRC := \
	../../hdl/bpRegMem.v \
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
pnr: $(BUILD)/$(PROJ).nextpnr.asc $(BUILD)/$(PROJ).arachne.asc
pack: $(BUILD)/$(PROJ).icepack.bin $(BUILD)/$(PROJ).arachne.icepack.bin
rpt: $(BUILD)/$(PROJ).icetime.rpt $(BUILD)/$(PROJ).arachne.icetime.rpt
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
		--asc $@

gui: $(PCF) $(BUILD)/$(PROJ).yosys.json
	nextpnr-ice40 --gui \
		--$(DEVICE) --package $(PACKAGE) --pcf $(PCF) \
		--json $*.yosys.json \
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
test: $(BUILD)/$(PROJ).icepack.bin
	bytePipe-utils -v --bitfile $< test

# Setup venv for Python 3.6+ ...
# pip install wavedrom
WAVEDROM_JSON = $(wildcard *.wavedrom.json)
WAVEDROM_SVG = $(WAVEDROM_JSON:.wavedrom.json=.wavedrom.svg)
wavedrom: $(WAVEDROM_SVG)
%.wavedrom.svg: %.wavedrom.json
	wavedrompy -i $^ -s $@

clean:
	rm -rf build
	rm -rf multipnr
	rm *.wavedrom.svg

.SECONDARY:
.PHONY: default all synth pnr pack rpt prog test wavedrom clean gui
