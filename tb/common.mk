
default: lint vcd

CC_SRC ?= $(TB).cc

V_INCDIRS ?=
V_INCDIRS += ../../hdl ../../verif
VERILATOR_INCDIRS := $(addprefix -I,$(V_INCDIRS))
IVERILOG_INCDIRS := $(addprefix -I,$(V_INCDIRS))

N_CYCLES ?= 100

BUILD ?= ./build
VCD_VERILATOR ?= $(BUILD)/$(TB).verilator.vcd
VCD_IVERILOG ?= $(BUILD)/$(TB).iverilog.vcd
VCDS := $(VCD_VERILATOR) $(VCD_IVERILOG)

verilator: $(VCD_VERILATOR)
iverilog: $(VCD_IVERILOG)
vcd: $(VCDS)

# Lint (check for undesirable pieces of code fluff) using Verilator.
LINT_SRC ?= $(wildcard *.v)
LINT_FLAGS := --lint-only $(VERILATOR_INCDIRS)
.PHONY: lint
lint:
	for f in $(LINT_SRC); do \
		verilator $(LINT_FLAGS) $$f; \
	done

# Verilator compile verilog into C++.
VERILATOR_TOP ?= $(TB)
VERILATOR_TRACE_DEPTH ?= 3
$(BUILD)/V$(TB).mk: $(V_SRC) $(CC_SRC) $(CC_H)
	mkdir -p $(BUILD)
	verilator --cc \
		--trace \
		--trace-depth $(VERILATOR_TRACE_DEPTH) \
		--exe \
		$(VERILATOR_INCDIRS) \
		--Mdir $(BUILD) \
		-DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -I../../../verif \
		--clk common_clk \
		--top-module $(VERILATOR_TOP) \
		$(CC_SRC) \
		$(VERILATOR_TOP).v

# Compile verilated C++ into executable.
$(BUILD)/V$(TB): $(BUILD)/V$(TB).mk
	make -j -C $(BUILD) -f V$(TB).mk V$(TB)

# Execute verilator object to dump VCD.
$(VCD_VERILATOR): $(BUILD)/V$(TB)
	time $(BUILD)/V$(TB) > $(BUILD)/$(TB).verilator.log
	@! grep -q ERROR $(BUILD)/$(TB).verilator.log

# Icarus (iverilog) compile verilog into executable VVP script.
IVERILOG_TOP ?= $(TB)
$(BUILD)/$(TB).vvp: $(V_SRC)
	mkdir -p $(BUILD)
	iverilog -g2005-sv \
		$(IVERILOG_INCDIRS) \
		-M$(BUILD)/$(TB).iverilog.deps \
		-DN_CYCLES=$(N_CYCLES) \
		-o $@ \
		-s $(IVERILOG_TOP) \
		$(V_SRC)

# Execute iverilog VVP script to dump VCD.
$(VCD_IVERILOG): $(BUILD)/$(TB).vvp
	time vvp $^ > $(BUILD)/$(TB).iverilog.log
	@! grep -q ERROR $(BUILD)/$(TB).iverilog.log

.PHONY: clean
clean:
	rm -rf $(BUILD)

.SECONDARY:

