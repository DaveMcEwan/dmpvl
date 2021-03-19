
default: lint_foss
default: default_ice40

SRC_SINGLEHIER += ../../hdl/edgeDetect.sv
SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/fpgaReset.sv
SRC_SINGLEHIER += usbPktTxMux.sv
SRC_SINGLEHIER += usbPktTx.sv
SRC_SINGLEHIER += usbPktRx.sv
SRC_SINGLEHIER += usbEpInArbiter.sv
SRC_SINGLEHIER += usbEpOutArbiter.sv
SRC_SINGLEHIER += usbPeIn.sv
SRC_SINGLEHIER += usbPeOut.sv

SRC_MULTIHIER += usbPe.sv
SRC_MULTIHIER += usbEpBridge.sv
SRC_MULTIHIER += usbCtrlSerial.sv
SRC_MULTIHIER += usbSerial.sv
SRC_MULTIHIER += top.sv

SRC_COMBINED := $(SRC_SINGLEHIER) $(SRC_MULTIHIER)

INCDIRS = . ../../hdl

# NOTE: VGWM design displeases Verilator greatly with many UNOPTFLAT warnings.
VERILATOR_SRC ?=
MK_LINT := ../../mk/lint.mk
include $(MK_LINT)

MK_PREPROC := ../../mk/preproc.mk
include $(MK_PREPROC)

YOSYS_SRC := $(SRC_SINGLEHIER) $(SRC_MULTIHIER) $(BUILD)/pll48.sv
#PNR_SEED ?= 1
MK_ICE40 := ../../mk/ice40.mk
include $(MK_ICE40)

MULTIPNR_ARACHNE := 1
MK_MULTIPNR := ../../mk/multipnr_ice40.mk
include $(MK_MULTIPNR)

MK_CLEAN := ../../mk/clean.mk
include $(MK_CLEAN)

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
