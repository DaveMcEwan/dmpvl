
# TinyFPGA-BX
DEVICE ?= lp8k
PACKAGE ?= cm81

PCF ?= pins.pcf

PROJ := top
BUILD := ./build

# Target fMax, not the PLL frequency.
# USB-FS design components are tied to a PLL frequency of 48MHz.
TGT_FMAX ?= 48

# NOTE: Finding a good seed requires some trials and won't necessarily be good
# for other setups (minor code changes, tool versions, host OS version, etc).
PNR_SEED ?= 5

default_ice40: pack rpt
synth: $(BUILD)/$(PROJ).yosys.json
pnr: $(BUILD)/$(PROJ).nextpnr.asc
pack: $(BUILD)/$(PROJ).icepack.bin
rpt: $(BUILD)/$(PROJ).icetime.rpt
.PHONY: default_ice40 synth pnr pack rpt

# TinyFPGA-BX has onboard 16MHz crystal oscillator.
PLL_INPUT_MHZ ?= 16
$(BUILD)/pll%.sv:
	mkdir -p $(BUILD)
	icepll \
		-q \
		-i $(PLL_INPUT_MHZ) \
		-o $* \
		-n pll$* \
		-m -f $@

# JSON netlist format - specific to yosys/nextpnr.
# BLIF netlist is usable with other tools, like Vivado and arachne-pnr.
YOSYS_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
YOSYS_INCDIRS ?= $(INCDIRS)
%.yosys.json: $(YOSYS_SRC)
	mkdir -p $(BUILD)
	yosys -q \
		-l $*.yosys.log \
		-p 'read_verilog -sv $(addprefix -I,$(YOSYS_INCDIRS)) $^' \
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

nextpnr_gui: $(PCF) $(BUILD)/$(PROJ).yosys.json
	nextpnr-ice40 --gui \
		--$(DEVICE) --package $(PACKAGE) --pcf $(PCF) \
		--json $(BUILD)/$(PROJ).yosys.json \
		--asc $(BUILD)/$(PROJ).asc
.PHONY: nextpnr_gui

%.icepack.bin: %.nextpnr.asc
	icepack $< $@

%.icetime.rpt: %.nextpnr.asc
	icetime -d $(DEVICE) -mtr $@ $<

prog: $(BUILD)/$(PROJ).icepack.bin
	tinyprog -p $<
.PHONY: prog


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
.PHONY: prog_arachne


CLEAN_PATHS += $(BUILD)
CLEAN_PATHS += $(*.wavedrom.svg)

.SECONDARY:
