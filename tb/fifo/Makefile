
N_CYCLES ?= 1000000

TB := fifo_tb

V_DEPS := \
	$(TB).v \
	../../hdl/fifo.v \

CPP_DEPS := \
	$(TB).cc \
	fifo_model.cc \
	fifo_model.h \
	fifo_utils.cc \
	fifo_utils.h

default: lint vcd

BUILD := ./build
VCD_VERILATOR := $(BUILD)/$(TB).verilator.vcd
VCD_IVERILOG := $(BUILD)/$(TB).iverilog.vcd
vcd: $(VCD_VERILATOR)
#vcd: $(VCD_IVERILOG)

.PHONY: lint
lint:
	verilator --lint-only -I../../hdl/ $(TB).v

# Verilator compile verilog into C++.
$(BUILD)/V$(TB).mk: $(V_DEPS) $(CPP_DEPS)
	mkdir -p $(BUILD)
	verilator --cc \
		--trace \
		--trace-depth 3 \
		--exe \
		-I../../hdl/ \
		--Mdir $(BUILD) \
		-DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -I../../../verif \
		--clk common_clk \
		--top-module $(TB) \
		../fifo_model.cc \
		../fifo_utils.cc \
		../$(TB).cc \
		$(TB).v

# Compile verilated C++ into executable.
$(BUILD)/V$(TB): $(BUILD)/V$(TB).mk
	make -j -C $(BUILD) -f V$(TB).mk V$(TB)

# Execute verilator object to dump VCD.
$(VCD_VERILATOR): $(BUILD)/V$(TB)
	time $(BUILD)/V$(TB) > $(BUILD)/$(TB).verilator.log
	@! grep -q ERROR $(BUILD)/$(TB).verilator.log

# TODO: iverilog sim

# Open VCDs in GtkWave.
.PHONY: waves
waves: $(VCD_VERILATOR)
	gtkwave $(VCD_VERILATOR) &
#	gtkwave $(VCD_IVERILOG) &

.PHONY: clean
clean:
	rm -rf $(BUILD)

.SECONDARY:
