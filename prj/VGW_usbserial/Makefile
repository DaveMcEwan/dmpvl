
# Hack repo from davidthings (David Williams) into multipnr.
# https://github.com/davidthings/tinyfpga_bx_usbserial
# make clean synth && make multipnr -j8 N_RUNS=1000

PCF = tinyfpga_bx_usbserial/pins.pcf

PROJ := top
BUILD := ./build
synth: $(BUILD)/$(PROJ).yosys.json
.PHONY: synth

MULTIPNR_NEXTPNR_LOG_RE := clk_48mhz_

MULTIPNR_MK := ../multipnr_ice40.mk
MULTIPNR_ARACHNE := 1
include $(MULTIPNR_MK)

$(BUILD)/$(PROJ).yosys.json:
	cd tinyfpga_bx_usbserial; git apply ../*.patch
	cd tinyfpga_bx_usbserial; make
	mkdir -p $(BUILD)
	cp tinyfpga_bx_usbserial/usbserial_tbx.json $(BUILD)/$(PROJ).yosys.json
	cp tinyfpga_bx_usbserial/usbserial_tbx.blif $(BUILD)/$(PROJ).yosys.blif

clean:
	cd tinyfpga_bx_usbserial; make clean
	cd tinyfpga_bx_usbserial; git reset --hard
	cd tinyfpga_bx_usbserial; make clean
	rm -rf $(BUILD)
