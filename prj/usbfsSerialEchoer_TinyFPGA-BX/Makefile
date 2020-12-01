
# Dave McEwan 2020-01-21

# TinyFPGA-BX
DEVICE ?= lp8k
PACKAGE ?= cm81
PCF ?= pins.pcf

PROJ := top
BUILD := ./build

SRC := \
	../../hdl/fifoW1R1.sv \
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
# TODO: Parameterize frequency of 48/60/72MHz
# High fMax (lots of slack), and low LUT usage is desirable.
# With the right value of PNR_SEED this can be up to 61MHz.
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
all: synth pnr pack rpt

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

# NOTE: Hardcoded device.
# NOTE: Use multipnr to find suitable seed.
# NOTE: arachne-pnr is now superceeded by nextpnr.
%.arachne.asc: $(PCF) %.yosys.json
	arachne-pnr \
		--device 8k \
		--package $(PACKAGE) \
		--seed 14 \
		--pcf-file $(PCF) \
		$*.yosys.blif \
		--output-file $@ 2> $*.arachne.log

%.arachne.icepack.bin: %.arachne.asc
	icepack $< $@

%.arachne.icetime.rpt: %.arachne.asc
	icetime -d $(DEVICE) -mtr $@ $<

prog_arachne: $(BUILD)/$(PROJ).arachne.icepack.bin
	tinyprog -p $<

clean:
	rm -rf build
	rm -rf multipnr

# Run place-and-route with different seed values to get a distribution of
# timing results.
# NOTE: Use the -j flag to parallelize runs.
# Put all asc,rpt,log files in ./multipnr/<seed>/*.{asc,rpt,log}
# Create a CSV log with these values:
#		seed, nextpnr.log, icetime.rpt, arachne.icetime.rpt
N_RUNS ?= 10
NUMBERS := $(shell seq 1 ${N_RUNS})
ASC_NEXTPNR := $(addprefix multipnr/,$(addsuffix /nextpnr.asc,${NUMBERS}))
RPT_NEXTPNR := $(addprefix multipnr/,$(addsuffix /nextpnr.rpt,${NUMBERS}))
ASC_ARACHNE := $(addprefix multipnr/,$(addsuffix /arachne.asc,${NUMBERS}))
RPT_ARACHNE := $(addprefix multipnr/,$(addsuffix /arachne.rpt,${NUMBERS}))
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

${ASC_ARACHNE}: multipnr/%/arachne.asc:
	mkdir -p $(@D)
	arachne-pnr \
		--device 8k \
		--package $(PACKAGE) \
		--seed $* \
		--pcf-file $(PCF) \
		$(BUILD)/$(PROJ).yosys.blif \
		--output-file $@ 2> $(@D)/arachne.log

${RPT_ARACHNE}: multipnr/%/arachne.rpt: multipnr/%/arachne.asc
	icetime -d $(DEVICE) -mtr $@ $<

multipnr/nextpnr.log.extracted: ${RPT_NEXTPNR}
	for f in multipnr/*/nextpnr.log; do \
		grep --with-filename 'Max frequency for clock' $$f | grep clk_48MHz_ | \
			tail -1 >> multipnr/nextpnr.log.extracted; \
	done

multipnr/nextpnr.rpt.extracted: ${RPT_NEXTPNR}
	grep -H 'Total path delay:' multipnr/*/nextpnr.rpt > \
		multipnr/nextpnr.rpt.extracted

multipnr/arachne.rpt.extracted: ${RPT_ARACHNE}
	-grep -H 'Total path delay:' multipnr/*/arachne.rpt > \
		multipnr/arachne.rpt.extracted

multipnr/results.csv.pdf: multipnr/nextpnr.log.extracted
multipnr/results.csv.pdf: multipnr/nextpnr.rpt.extracted
multipnr/results.csv.pdf: multipnr/arachne.rpt.extracted
multipnr/results.csv.pdf:
	python3.7 multipnrAnalyze.py

.PHONY: multipnr
multipnr: $(PCF) $(BUILD)/$(PROJ).yosys.json
multipnr: multipnr/results.csv.pdf

.SECONDARY:
.PHONY: default all synth pnr pack rpt prog clean gui
