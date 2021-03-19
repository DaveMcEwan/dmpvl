
INCDIRS ?= . ../../hdl ../../verif
TB ?= $(shell basename $(PWD))_tb

vcd: verilator_vcd
vcd: iverilog_vcd

MK_LINT := ../../mk/lint.mk
include $(MK_LINT)

MK_CLEAN := ../../mk/clean.mk
include $(MK_CLEAN)

CC_SRC ?= $(TB).cc

# External objects for DPI imports.
$(BUILD)/ptyBytePipe.o: ../../verif/ptyBytePipe.c
	$(CC) $(CPPFLAGS) $(CFLAGS) -c -o $@ $<

VERILATOR_TRACE_DEPTH ?= 3

VERILATOR_SRC ?= $(filter-out $(VERILATOR_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
VERILATOR_INCDIRS ?= $(INCDIRS)
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_C_INCDIRS ?= ../../../verif
VERILATOR_DPI_DEPS := $(addprefix $(BUILD)/,$(DPI_OBJS))
VERILATOR_TB_TOP ?= $(TB)
VERILATOR_TB_VCD ?= $(BUILD)/$(TB).verilator.vcd
VERILATOR_TB_LOGFILE := $(basename $(VERILATOR_TB_VCD))

VERILATOR_TB_FLAGS := --cc $(VERILATOR_LANG) $(addprefix -I,$(VERILATOR_INCDIRS))
VERILATOR_TB_FLAGS += --trace --trace-depth $(VERILATOR_TRACE_DEPTH)
VERILATOR_TB_FLAGS += --exe
VERILATOR_TB_FLAGS += --Mdir $(BUILD)
VERILATOR_TB_FLAGS += -DN_CYCLES=$(N_CYCLES) -CFLAGS -DN_CYCLES=$(N_CYCLES)
VERILATOR_TB_FLAGS += $(addprefix -CFLAGS -I,$(VERILATOR_C_INCDIRS))
VERILATOR_TB_FLAGS += $(addprefix -LDFLAGS ,$(notdir $(VERILATOR_DPI_DEPS)))
VERILATOR_TB_FLAGS += --clk common_clk
VERILATOR_TB_FLAGS += --top-module $(VERILATOR_TB_TOP)
VERILATOR_TB_FLAGS += $(CC_SRC)

verilator_vcd: $(VERILATOR_TB_VCD)

# Verilator compile verilog into C++.
$(BUILD)/V$(TB).mk: $(VERILATOR_SRC) $(CC_SRC) $(CC_H)
	mkdir -p $(BUILD)
	verilator $(VERILATOR_TB_FLAGS) $(VERILATOR_TB_TOP).sv

# Compile verilated C++ into executable.
$(BUILD)/V$(TB): $(BUILD)/V$(TB).mk $(VERILATOR_DPI_DEPS)
	make -j -C $(BUILD) -f V$(TB).mk V$(TB)

# Execute verilator object to dump VCD.
$(VERILATOR_TB_VCD): $(BUILD)/V$(TB)
	time $(BUILD)/V$(TB) > $(VERILATOR_TB_LOGFILE)
	! grep -q ERROR $(VERILATOR_TB_LOGFILE)


IVERILOG_SRC ?= $(filter-out $(IVERILOG_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
IVERILOG_INCDIRS ?= $(INCDIRS)
IVERILOG_LANG ?= -g2005-sv
IVERILOG_TB_TOP ?= $(TB)
IVERILOG_TB_VCD ?= $(BUILD)/$(TB).iverilog.vcd
IVERILOG_TB_LOGFILE := $(basename $(IVERILOG_TB_VCD))

IVERILOG_TB_FLAGS := $(IVERILOG_LANG) $(addprefix -I,$(IVERILOG_INCDIRS))
IVERILOG_TB_FLAGS += -M$(BUILD)/$(TB).iverilog.deps
IVERILOG_TB_FLAGS += -DN_CYCLES=$(N_CYCLES)
IVERILOG_TB_FLAGS += -s $(IVERILOG_TB_TOP)

iverilog_vcd: $(IVERILOG_TB_VCD)

# Icarus (iverilog) compile verilog into executable VVP script.
$(BUILD)/$(TB).vvp: $(IVERILOG_SRC)
	mkdir -p $(BUILD)
	iverilog $(IVERILOG_TB_FLAGS) -o $@ $(IVERILOG_SRC)

# Execute iverilog VVP script to dump VCD.
$(IVERILOG_TB_VCD): $(BUILD)/$(TB).vvp
	time vvp $^ > $(IVERILOG_TB_LOGFILE)
	! grep -q ERROR $(IVERILOG_TB_LOGFILE)

