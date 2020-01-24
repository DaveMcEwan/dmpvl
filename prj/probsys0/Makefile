
BUILD = ./build
PROJ = probsys0
N_CYCLES ?= 100

VCD_VERILATOR = $(BUILD)/$(PROJ).verilator.vcd
VCD_IVERILOG = $(BUILD)/$(PROJ).iverilog.vcd

default: lint vcd

vcd: $(VCD_VERILATOR)
#vcd: $(VCD_IVERILOG)

SRC = \
	$(PROJ).v \
	../../hdl/resetDetect.v \
	../../hdl/prngXoroshiro128p.v \
	../../hdl/fifo.v \
	../../hdl/axi4liteMonitor.v \
	../../hdl/axi4liteRandomSlave.v \
	../../hdl/axi4liteRandomMaster.v

.PHONY: lint
lint:
	verilator --lint-only -I../../hdl/ $(PROJ).v

# Verilator compile verilog into C++.
#		-DABSTRACT_PRNG=1
$(BUILD)/V$(PROJ).mk: $(SRC)
	mkdir -p $(BUILD)
	verilator --cc \
		--trace \
		--trace-depth 3 \
		--exe \
		-I../../hdl/ \
		--Mdir $(BUILD) \
		-DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -I../../../verif/ \
		--clk i_clk \
		--top-module $(PROJ) \
		../$(PROJ).cc \
		$(PROJ).v

# Compile verilated C++ into executable.
$(BUILD)/V$(PROJ): $(BUILD)/V$(PROJ).mk
	make -j -C $(BUILD) -f V$(PROJ).mk V$(PROJ)

# Execute verilated object to dump VCD.
$(VCD_VERILATOR): $(BUILD)/V$(PROJ)
	$(BUILD)/V$(PROJ) > $(BUILD)/$(PROJ).verilator.log

# TODO: iverilog sim

# Open VCDs in GtkWave.
.PHONY: waves
waves: $(VCD_VERILATOR)
	gtkwave $(VCD_VERILATOR) &
#	gtkwave $(VCD_IVERILOG) &

.PHONY: clean
clean:
	rm -rf $(BUILD)
	rm -rf $(VCD_VERILATOR)
	rm -rf $(VCD_IVERILOG)

.SECONDARY:
