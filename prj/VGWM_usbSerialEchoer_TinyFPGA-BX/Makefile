
# TinyFPGA-BX
DEVICE ?= lp8k
PACKAGE ?= cm81
PCF ?= pins.pcf

PROJ := top
BUILD := ./build

SRC = \
	../../hdl/edgeDetect.v \
	../../hdl/fifo.v \
	usbPktTxMux.v \
	usbPktTx.v \
	usbPktRx.v \
	usbEpInArbiter.v \
	usbEpOutArbiter.v \
	usbPeIn.v \
	usbPeOut.v \
	usbPe.v \
	usbEpBridge.v \
	usbCtrlSerial.v \
	usbSerial.v \
	$(BUILD)/pll48.v \
	$(PROJ).v

# Target fMax, not the PLL frequency.
# This design is tied to a PLL frequency of 48MHz.
# High fMax (lots of slack), and low LUT usage is desirable.
# With the right value of PNR_SEED this can be up to 58MHz.
TGT_FMAX = 48

# NOTE: Finding a good seed requires some trials and won't necessarily be good
# for other setups (minor code changes, tool versions, host OS version, etc).
# Use multipnr to find a suitable seed.
PNR_SEED ?= 5

default: lint iverilog $(BUILD)/$(PROJ).icetime.rpt $(BUILD)/$(PROJ).icepack.bin

synth: $(BUILD)/$(PROJ).yosys.json
pnr: $(BUILD)/$(PROJ).nextpnr.asc $(BUILD)/$(PROJ).arachne.asc
pack: $(BUILD)/$(PROJ).icepack.bin $(BUILD)/$(PROJ).arachne.icepack.bin
rpt: $(BUILD)/$(PROJ).icetime.rpt $(BUILD)/$(PROJ).arachne.icetime.rpt
all: lint iverilog synth pnr pack rpt

# Use Verilator's LINT mode to ensure there's nothing too obviously wrong.
# This also ensures files are compatible with verilator.
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I../../hdl
lint:
	verilator $(VERILATOR_FLAGS) usbPktTxMux.v
	verilator $(VERILATOR_FLAGS) usbPktTx.v
	verilator $(VERILATOR_FLAGS) usbPktRx.v
	verilator $(VERILATOR_FLAGS) usbEpInArbiter.v
	verilator $(VERILATOR_FLAGS) usbEpOutArbiter.v
	verilator $(VERILATOR_FLAGS) usbPeIn.v
	verilator $(VERILATOR_FLAGS) usbPeOut.v
	verilator $(VERILATOR_FLAGS) usbPe.v
	verilator $(VERILATOR_FLAGS) usbEpBridge.v
	verilator $(VERILATOR_FLAGS) usbCtrlSerial.v

# Run through iverilog (Icarus) to ensure files are compatible.
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I../../hdl
iverilog:
	iverilog $(IVERILOG_FLAGS) usbPktTxMux.v
	iverilog $(IVERILOG_FLAGS) usbPktTx.v
	iverilog $(IVERILOG_FLAGS) usbPktRx.v
	iverilog $(IVERILOG_FLAGS) usbEpInArbiter.v
	iverilog $(IVERILOG_FLAGS) usbEpOutArbiter.v
	iverilog $(IVERILOG_FLAGS) usbPeIn.v
	iverilog $(IVERILOG_FLAGS) usbPeOut.v
	iverilog $(IVERILOG_FLAGS) -i usbPe.v
	iverilog $(IVERILOG_FLAGS) -i usbEpBridge.v
	iverilog $(IVERILOG_FLAGS) -i usbCtrlSerial.v
	iverilog $(IVERILOG_FLAGS) -i usbSerial.v

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


# {{{ WIP

# Separate build directory for noisy proprietary tools.
BUILD_ICECUBE2 := ./build.icecube2

# NOTE: iCEcube2/SynplifyPro requires significant setup.
# https://forums.linuxmint.com/viewtopic.php?t=290906
# TODO: Document required setup of these environment variables:
#   - FOUNDRY
#   - SBT_DIR
#   - SYNPLIFY_PATH
#   - TCL_LIBRARY
#   - LM_LICENSE_FILE
#   - LD_LIBRARY_PATH
# Create a dummy NIC called eth0 with MAC address to match the license file.
# NOTE: You may need to request a more recent one, valid for 1 year.
#   sudo ip link add eth0 type dummy
#   sudo ip link set eth0 address 00:11:22:33:44:55
#   export LM_LICENSE_FILE=$PWD/icecube2_001122334455_license.dat
ICECUBE2DIR ?= /space/lattice/lscc/iCEcube2.2017.08
FOUNDRY := $(ICECUBE2DIR)/LSE
SBT_DIR := $(ICECUBE2DIR)/sbt_backend
SYNPLIFY_PATH := $(ICECUBE2DIR)/synpbase
TCL_LIBRARY := $(SBT_DIR)/bin/linux/lib/tcl8.4

synp: $(BUILD_ICECUBE2)/$(PROJ).synplifypro.edf
bknd: $(BUILD_ICECUBE2)/$(PROJ).icecube2.bin

# Synthesize to EDIF netlist.
# SynplifyPro (a Synopsys tool) is required instead of LSE (Lattice Synthesis
# Engine) because LSE supports only Verilog2001.
%.synplifypro.edf: synplifypro.prj $(SRC)
	mkdir -p $(BUILD_ICECUBE2)
	$(SBT_DIR)/bin/linux/opt/synpwrap/synpwrap -prj $< -nolog > /dev/null
	-mv ./synlog.tcl $(BUILD_ICECUBE2)
	-mv ./stdout.log $(BUILD_ICECUBE2)
	rm -f ./stdout.log.bak

# iCEcube2 backend default flow.
$(BUILD_ICECUBE2)/$(PROJ).icecube2.bin: $(BUILD_ICECUBE2)/$(PROJ).synplifypro.edf
	./icecube2Backend.tcl
	cp $(BUILD_ICECUBE2)/sbt/outputs/bitmap/$(PROJ)_bitmap.bin $@

# TODO: bin to asc, `icepack -u`

# }}} WIP


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
		grep --with-filename 'Max frequency for clock' $$f | \
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
