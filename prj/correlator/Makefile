
# Dave McEwan 2020-04-23

# TinyFPGA-BX
DEVICE ?= lp8k
PACKAGE ?= cm81
PCF ?= pins.pcf

PROJ := top
BUILD := ./build

SRC := \
	../../hdl/fpgaReset.sv \
	../../hdl/usbfsPktRx.sv \
	../../hdl/usbfsPktTx.sv \
	../../hdl/usbfsTxn.sv \
	../../hdl/usbfsEndpRx.sv \
	../../hdl/usbfsEndpTx.sv \
	../../hdl/usbfsEndpCtrlSerial.sv \
	../../hdl/usbfsSerial.sv \
	$(BUILD)/pll48.sv \
	../../hdl/fifo.sv \
	../../hdl/fxcs.sv \
	../../hdl/logdropWindow.sv \
	../../hdl/mssbIdx.sv \
	../../hdl/onehotIdx.sv \
	../../hdl/prngXoshiro128p.sv \
	../../hdl/strobe.sv \
	../../hdl/pwm.sv \
	../../hdl/dividerFsm.sv \
	correlator.sv \
	corrCountRect.sv \
	corrCountLogdrop.sv \
	bpReg.sv \
	$(PROJ).sv

# Target fMax, not the PLL frequency.
# The design components are tied to a PLL frequency of 48MHz.
TGT_FMAX = 48

# NOTE: Finding a good seed requires some trials and won't necessarily be good
# for other setups (minor code changes, tool versions, host OS version, etc).
# Use multipnr to find a suitable seed.
PNR_SEED ?= 5

default: lint iverilog $(BUILD)/$(PROJ).icetime.rpt $(BUILD)/$(PROJ).icepack.bin

synth: $(BUILD)/$(PROJ).yosys.json
pnr: $(BUILD)/$(PROJ).nextpnr.asc
pack: $(BUILD)/$(PROJ).icepack.bin
rpt: $(BUILD)/$(PROJ).icetime.rpt
all: lint iverilog synth pnr pack rpt

# Use Verilator's LINT mode to ensure there's nothing too obviously wrong.
# This also ensures files are compatible with verilator.
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I../../hdl
lint:
	verilator $(VERILATOR_FLAGS) bpReg.sv
	verilator $(VERILATOR_FLAGS) corrCountRect.sv
	verilator $(VERILATOR_FLAGS) corrCountLogdrop.sv
	verilator $(VERILATOR_FLAGS) correlator.sv

# Run through iverilog (Icarus) to ensure files are compatible.
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I../../hdl
iverilog:
	iverilog $(IVERILOG_FLAGS) -i bpReg.sv
	iverilog $(IVERILOG_FLAGS) corrCountRect.sv
	iverilog $(IVERILOG_FLAGS) -i corrCountLogdrop.sv
	iverilog $(IVERILOG_FLAGS) -i correlator.sv

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

clean:
	rm -rf build
	rm -rf multipnr

.SECONDARY:
.PHONY: default all synth pnr pack rpt prog clean gui
