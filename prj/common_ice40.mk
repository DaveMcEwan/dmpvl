

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

default: lint $(BUILD)/$(PROJ).icetime.rpt $(BUILD)/$(PROJ).icepack.bin

synth: $(BUILD)/$(PROJ).yosys.json
pnr: $(BUILD)/$(PROJ).nextpnr.asc
pack: $(BUILD)/$(PROJ).icepack.bin
rpt: $(BUILD)/$(PROJ).icetime.rpt
all: lint synth pnr pack rpt

# Read in design files with a variety of tools to ensure there's nothing too
# obviously wrong.
lint: lint_verilator lint_iverilog lint_yosys
.PHONY: lint lint_verilator lint_iverilog lint_yosys

VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I../../hdl
lint_verilator: $(addprefix lint_verilator/,$(LINT_VERILATOR_SRC))
lint_verilator/%:
	verilator $(VERILATOR_FLAGS) $*

IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I../../hdl
lint_iverilog: $(addprefix lint_iverilog/,$(LINT_IVERILOG_SRC))
lint_iverilog/%:
	iverilog $(IVERILOG_FLAGS) -i $*

lint_yosys: $(addprefix lint_yosys/,$(LINT_YOSYS_SRC))
lint_yosys/%:
	yosys -q -p 'read_verilog -sv -I../../hdl/ $*'

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
		--json $(BUILD)/$(PROJ).yosys.json \
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
	rm -f *.wavedrom.svg

.SECONDARY:
.PHONY: default all synth pnr pack rpt prog clean gui
