
# Usage:
# make pp_src			# Just run Verilator preprocessor on sources.
# make lint				# Just syntax check with all the tools.
# make tb				# Just build the testbenches.
# make sw/hello			# Builds memory image and puts it into sw.hex.
# make iverilog			# Runs Icarus simulation with current sw.hex.
# make verilator		# Runs Verilator simulation with current sw.hex.
# make hello			# Build memory image, run Icarus, run Verilator.

BUILD := ./build

RISCV_BIN := $(RISCV)/bin/riscv32-unknown-elf-
# The enviroment variable RISCV should point to riscv-tools:
# https://github.com/riscv/riscv-tools
#	OR if you've built the toolchain separately (a la picorv32)
#RISCV_BIN := /space/riscv32imc/bin/riscv32-unknown-elf-

MARCH = rv32i
GCC_WARNS += -Werror
GCC_WARNS += -Wall
GCC_WARNS += -Wextra
GCC_WARNS += -Wundef
GCC_WARNS += -Wpointer-arith
GCC_WARNS += -Wcast-qual
GCC_WARNS += -Wcast-align
GCC_WARNS += -Wwrite-strings
GCC_WARNS += -Wredundant-decls
GCC_WARNS += -Wstrict-prototypes
GCC_WARNS += -pedantic
#GCC_WARNS += -Wconversion

DUMPLEVEL ?= 0
TRACEDEPTH := $(shell expr $(DUMPLEVEL) + 1)


MEM_N_KBYTE = 64

default: lint
default: hello

# Verilator has the best preprocessor by far, and is required for the ff_
# macros so put the expanded source files in the build directory.
PREPROCESSED_SRCS = $(BUILD)/rsm_hier.sv
$(BUILD)/%.sv: hw/%.sv
	mkdir -p $(BUILD)
	verilator -E $< --Mdir $(BUILD)/obj_dir > $@
pp_src: $(PREPROCESSED_SRCS)

lint: pp_src
	verilator --lint-only --Mdir $(BUILD)/obj_dir $(BUILD)/rsm_hier.sv
	yosys -q -p 'read_verilog $(BUILD)/rsm_hier.sv'
	iverilog -g2001 -s rsm_m -o $(BUILD)/rsm_hier.vvp $(BUILD)/rsm_hier.sv

# Compile and elaborate icarus testbench.
$(BUILD)/testbench.vvp: pp_src
	iverilog -g2001 -s testbench \
		-DMEM_N_KBYTE=$(MEM_N_KBYTE) \
		-o $(BUILD)/testbench.vvp tb/testbench.sv

# Run icarus testbench, dumping VCD.
$(BUILD)/testbench.iverilog.vcd: $(BUILD)/testbench.vvp
	vvp -N $< +vcd +dumplevel=$(DUMPLEVEL)

# Compile verilator testbench.
$(BUILD)/obj_dir/Vtestbench: pp_src
$(BUILD)/obj_dir/Vtestbench: tb/testbench.cc
$(BUILD)/obj_dir/Vtestbench: tb/testbench.sv
	verilator --cc --exe --Mdir $(BUILD)/obj_dir \
		--trace --trace-depth $(TRACEDEPTH) \
		-Wno-fatal \
		-DMEM_N_KBYTE=$(MEM_N_KBYTE) \
		--top-module testbench \
		--clk i_clk \
		../../tb/testbench.cc \
		tb/testbench.sv
	$(MAKE) -C $(BUILD)/obj_dir -f Vtestbench.mk

# Compile all testbenches ready to run.
tb: $(BUILD)/testbench.vvp
tb: $(BUILD)/obj_dir/Vtestbench

# Run Icarus with whatever was compiled into build/sw.hex.
IVERILOG_VCD = $(BUILD)/testbench.iverilog.vcd
iverilog: $(BUILD)/testbench.vvp
	vvp -N $(BUILD)/testbench.vvp +vcd +dumplevel=$(DUMPLEVEL)
#	mv $(IVERILOG_VCD) $(IVERILOG_VCD).unpruned
#	tb/vcdprune $(IVERILOG_VCD).unpruned -o $(IVERILOG_VCD)

# Run Verilator with whatever was compiled into build/sw.hex.
VERILATOR_VCD = $(BUILD)/testbench.verilator.vcd
verilator: $(BUILD)/obj_dir/Vtestbench
	$(BUILD)/obj_dir/Vtestbench
#	mv $(VERILATOR_VCD) $(VERILATOR_VCD).unpruned
#	tb/vcdprune $(VERILATOR_VCD).unpruned -o $(VERILATOR_VCD)


$(BUILD)/%.o: sw/%.S
	mkdir -p $(shell dirname $@)
	$(RISCV_BIN)gcc -c -march=$(MARCH) -o $@ $<

$(BUILD)/%.o: sw/%.c
	mkdir -p $(shell dirname $@)
	$(RISCV_BIN)gcc -c $(GCC_WARNS) -Os --std=c99 -ffreestanding -nostdlib \
		-Isw -march=$(MARCH) -o $@ $<

RISCV_LINK = $(RISCV_BIN)gcc -Os -ffreestanding -nostdlib
RISCV_LINK += -Wl,-Bstatic,-T,sw/sections.lds,-Map,$@.map,--strip-debug

%.bin: %.elf
	chmod -x $<
	$(RISCV_BIN)objdump -D $< > $<.dasm
	$(RISCV_BIN)objcopy -O binary $< $@
	chmod -x $@

%.hex: %.bin sw/makehex.py
	python3 sw/makehex.py $< $(MEM_N_KBYTE) > $@
	cp $@ $(BUILD)/sw.hex


HELLO_OBJS := $(BUILD)/start.o
HELLO_OBJS += $(BUILD)/tb.o
HELLO_OBJS += $(BUILD)/hello/main.o
$(BUILD)/hello/hello.elf: $(HELLO_OBJS) sw/sections.lds
	$(RISCV_LINK) -o $@ $(HELLO_OBJS) -lm -lgcc
sw/hello: $(BUILD)/hello/hello.hex
hello: sw/hello iverilog verilator

$(BUILD)/tests/%.o: sw/tests/%.S sw/tests/riscv_test.h sw/tests/test_macros.h
	mkdir -p $(shell dirname $@)
	$(RISCV_BIN)gcc -c -march=$(MARCH) -o $@ -DTEST_FUNC_NAME=$(notdir $(basename $<)) \
		-DTEST_FUNC_TXT='"$(notdir $(basename $<))"' -DTEST_FUNC_RET=$(notdir $(basename $<))_ret $<

TESTS_OBJS = $(addprefix $(BUILD)/tests/, $(notdir $(addsuffix .o, $(basename $(wildcard sw/tests/*.S)))))
$(BUILD)/tests/tests.elf: $(TESTS_OBJS) sw/sections.lds
	$(RISCV_LINK) -o $@ $(BUILD)/tests/main.o $(patsubst %/main.o,,$(TESTS_OBJS)) -lm -lgcc
sw/tests: $(BUILD)/tests/tests.hex
tests: sw/tests iverilog verilator


clean:
	rm -rf $(BUILD)
