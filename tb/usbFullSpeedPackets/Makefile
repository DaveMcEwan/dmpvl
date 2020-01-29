
TB := usbFullSpeedPackets_tb

SRC := \
	../../hdl/resetDetect.v \
	../../hdl/usbfsPktRx.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktRx.v \
	../../verif/generateClock.v \
	../../verif/usbFullSpeedPacketSender.v \
	../../verif/usbFullSpeedPacketReceiver.v \
	drivePackets.v \
	$(TB).v

default: lint vcd

BUILD := ./build
VCD_VERILATOR := $(BUILD)/$(TB).verilator.vcd
VCD_IVERILOG := $(BUILD)/$(TB).iverilog.vcd
#vcd: $(VCD_VERILATOR)
vcd: $(VCD_IVERILOG)

.PHONY: lint
lint:
	verilator --lint-only -I../../hdl/ drivePackets.v
#	verilator --lint-only -I../../hdl/ $(TB).v

# Verilator compile verilog into C++.
$(BUILD)/V$(TB).mk: $(SRC)
	mkdir -p $(BUILD)
	verilator --cc \
		--trace \
		--trace-depth 3 \
		--exe \
		-I../../hdl/ \
		-I../../verif/ \
		--Mdir $(BUILD) \
		-CFLAGS -I../../../verif \
		--top-module $(TB) \
		../$(TB).cc \
		$(TB).v

# Compile verilated C++ into executable.
$(BUILD)/V$(TB): $(BUILD)/V$(TB).mk
	make -j -C $(BUILD) -f V$(TB).mk V$(TB)

# Execute verilator object to dump VCD.
$(VCD_VERILATOR): $(BUILD)/V$(TB)
	time $(BUILD)/V$(TB) > $(BUILD)/$(TB).verilator.log
	@! grep -q ERROR $(BUILD)/$(TB).verilator.log

# Icarus (iverilog) compile verilog into executable VVP script.
$(BUILD)/$(TB).vvp: $(SRC)
	mkdir -p $(BUILD)
	iverilog -g2005-sv \
		-I../../hdl \
		-I../../verif \
		-M$(BUILD)/$(TB).iverilog.deps \
		-o $@ \
		-s $(TB) \
		$(SRC)

# Execute iverilog VVP script to dump VCD.
$(VCD_IVERILOG): $(BUILD)/$(TB).vvp
	time vvp $^ > $(BUILD)/$(TB).iverilog.log
	@! grep -q ERROR $(BUILD)/$(TB).iverilog.log

# Open VCDs in GtkWave.
.PHONY: waves
waves: $(VCD_VERILATOR)
	gtkwave $(VCD_IVERILOG) &
#	gtkwave $(VCD_VERILATOR) &

.PHONY: clean
clean:
	rm -rf $(BUILD)

.SECONDARY:
