
# TinyFPGA-BX
DEVICE ?= lp8k
PACKAGE ?= cm81
PCF ?= pins.pcf

PROJ := top
BUILD := ./build

SRC := \
	../../hdl/edgeDetect.sv \
	../../hdl/fifoW1R1.sv \
	../../hdl/fpgaReset.sv \
	usbPktTxMux.sv \
	usbPktTx.sv \
	usbPktRx.sv \
	usbEpInArbiter.sv \
	usbEpOutArbiter.sv \
	usbPeIn.sv \
	usbPeOut.sv \
	usbPe.sv \
	usbEpBridge.sv \
	usbCtrlSerial.sv \
	usbSerial.sv \
	$(BUILD)/pll48.sv \
	$(PROJ).sv

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
	verilator $(VERILATOR_FLAGS) usbPktTxMux.sv
	verilator $(VERILATOR_FLAGS) usbPktTx.sv
	verilator $(VERILATOR_FLAGS) usbPktRx.sv
	verilator $(VERILATOR_FLAGS) usbEpInArbiter.sv
	verilator $(VERILATOR_FLAGS) usbEpOutArbiter.sv
	verilator $(VERILATOR_FLAGS) usbPeIn.sv
	verilator $(VERILATOR_FLAGS) usbPeOut.sv
	verilator $(VERILATOR_FLAGS) usbPe.sv
	verilator $(VERILATOR_FLAGS) usbEpBridge.sv
	verilator $(VERILATOR_FLAGS) usbCtrlSerial.sv

# Run through iverilog (Icarus) to ensure files are compatible.
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I../../hdl
iverilog:
	iverilog $(IVERILOG_FLAGS) usbPktTxMux.sv
	iverilog $(IVERILOG_FLAGS) usbPktTx.sv
	iverilog $(IVERILOG_FLAGS) usbPktRx.sv
	iverilog $(IVERILOG_FLAGS) usbEpInArbiter.sv
	iverilog $(IVERILOG_FLAGS) usbEpOutArbiter.sv
	iverilog $(IVERILOG_FLAGS) usbPeIn.sv
	iverilog $(IVERILOG_FLAGS) usbPeOut.sv
	iverilog $(IVERILOG_FLAGS) -i usbPe.sv
	iverilog $(IVERILOG_FLAGS) -i usbEpBridge.sv
	iverilog $(IVERILOG_FLAGS) -i usbCtrlSerial.sv
	iverilog $(IVERILOG_FLAGS) -i usbSerial.sv

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

.SECONDARY:
.PHONY: default all lint iverilog synth pnr pack rpt prog clean gui

MULTIPNR_MK := ../multipnr_ice40/multipnr_ice40.mk
MULTIPNR_ARACHNE := 1
include $(MULTIPNR_MK)
