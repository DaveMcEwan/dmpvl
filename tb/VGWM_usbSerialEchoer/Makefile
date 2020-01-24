
TB := VGWM_usbSerialEchoer_tb

SRC := \
	../../verif/generateClock.v \
	../../verif/tristateBuffer.v \
	../../hdl/resetDetect.v \
	../../hdl/edgeDetect.v \
	../../hdl/fifo.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktTxMux.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktTx.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPktRx.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpInArbiter.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpOutArbiter.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPeIn.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPeOut.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbPe.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbCtrlSerial.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbEpBridge.v \
	../../prj/VGWM_usbSerialEchoer_TinyFPGA-BX/usbSerial.v \
	../../verif/usbFullSpeedPacketSender.v \
	../../verif/usbFullSpeedPacketReceiver.v \
	../../verif/usbFullSpeedTransactor.v \
	driveHost.v \
	$(TB).v

default: lint vcd

BUILD := ./build
VCD_VERILATOR := $(BUILD)/$(TB).verilator.vcd
VCD_IVERILOG := $(BUILD)/$(TB).iverilog.vcd
#vcd: $(VCD_VERILATOR)
vcd: $(VCD_IVERILOG)

LINT_FLAGS := --lint-only -I../../hdl -I../../verif
.PHONY: lint
lint:
	verilator $(LINT_FLAGS) driveHost.v
#	verilator $(LINT_FLAGS) $(TB).v

# Verilator compile verilog into C++.
$(BUILD)/V$(TB).mk: $(SRC)
	mkdir -p $(BUILD)
	verilator --cc \
		--trace \
		--trace-depth 3 \
		--exe \
		-I../../hdl/ \
		--Mdir $(BUILD) \
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
