
# Dave McEwan 2020-05-03

# TinyFPGA-BX
DEVICE ?= lp8k
PACKAGE ?= cm81
PCF ?= pins.pcf

PROJ := top
BUILD := ./build

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
	../../hdl/fifo.sv \
	../../hdl/fpgaReset.sv \
	../../hdl/usbfsPktRx.sv \
	../../hdl/usbfsPktTx.sv \
	../../hdl/usbfsTxn.sv \
	../../hdl/usbfsEndpRx.sv \
	../../hdl/usbfsEndpTx.sv \
	../../hdl/usbfsEndpCtrlSerial.sv \
	../../hdl/usbfsSerial.sv \
	$(BUILD)/pll48.sv \
	$(PROJ).sv

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

$(BUILD)/pll48.sv:
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

# Run place-and-route with different seed values to get a distribution of
# timing results.
# NOTE: Use the -j flag to parallelize runs.
# Put all asc,rpt,log files in ./multipnr/<seed>/*.{asc,rpt,log}
# Create a CSV log with these values:
#		seed, nextpnr.log, icetime.rpt
N_RUNS ?= 10
NUMBERS := $(shell seq 1 ${N_RUNS})
ASC_NEXTPNR := $(addprefix multipnr/,$(addsuffix /nextpnr.asc,${NUMBERS}))
RPT_NEXTPNR := $(addprefix multipnr/,$(addsuffix /nextpnr.rpt,${NUMBERS}))
multipnr/%/nextpnr.asc:
	mkdir -p $(@D)
	nextpnr-ice40 -q \
		--$(DEVICE) --package $(PACKAGE) --pcf $(PCF) \
		-l $(@D)/nextpnr.log \
		--seed $* \
		--opt-timing \
		--json $(BUILD)/$(PROJ).yosys.json \
		--asc $@

${RPT_NEXTPNR}: multipnr/%/nextpnr.rpt: multipnr/%/nextpnr.asc
	icetime -d $(DEVICE) -mtr $@ $<

multipnr/nextpnr.log.extracted: ${RPT_NEXTPNR}
	for f in multipnr/*/nextpnr.log; do \
		grep --with-filename 'Max frequency for clock' $$f | grep clk_48MHz_ | \
			tail -1 >> multipnr/nextpnr.log.extracted; \
	done

multipnr/nextpnr.rpt.extracted: ${RPT_NEXTPNR}
	grep -H 'Total path delay:' multipnr/*/nextpnr.rpt > \
		multipnr/nextpnr.rpt.extracted

multipnr/results.csv.pdf: multipnr/nextpnr.log.extracted
multipnr/results.csv.pdf: multipnr/nextpnr.rpt.extracted
multipnr/results.csv.pdf:
	python3.7 multipnrAnalyze.py

.PHONY: multipnr
multipnr: $(PCF) $(BUILD)/$(PROJ).yosys.json
multipnr: multipnr/results.csv.pdf

.SECONDARY:
.PHONY: default all synth pnr pack rpt prog test clean gui
