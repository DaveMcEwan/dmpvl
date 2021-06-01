
BUILD ?= ./build
TB ?= $(shell basename $(PWD))_tb
N_CYCLES ?= 1000000

INCDIRS ?= . ../../hdl ../../verif

SRC_SINGLEHIER += ../../hdl/binToGray.sv
SRC_SINGLEHIER += ../../hdl/grayToBin.sv
SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/syncBit.sv

SRC_MULTIHIER += ../../hdl/cdcData.sv
SRC_MULTIHIER += ../../hdl/cdcFifo.sv

CC_SRC += ../../verif/modelPrint.cc

CC_H += ../../verif/modelPrint.h

SRC_MULTIHIER += $(TB).sv
CC_SRC += $(TB).cc

default: all

MK_CLEAN := ../../mk/clean.mk
include $(MK_CLEAN)

MK_CSV = ../../mk/csv.mk
include $(MK_CSV)

ALL_TB_VERILATOR_VCD := $(addprefix $(BUILD)/,$(addsuffix /$(TB).verilator.fst,$(CSV_ROWS)))
.PHONY: all
all: $(ALL_TB_VERILATOR_VCD)
	@echo $(TB) PASSED

VERILATOR_TRACE_DEPTH ?= 3

VERILATOR_SRC ?= $(filter-out $(VERILATOR_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
VERILATOR_INCDIRS ?= $(INCDIRS)
VERILATOR_TB_FLAGS := --cc $(VERILATOR_LANG) $(addprefix -I,$(VERILATOR_INCDIRS))
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_C_INCDIRS ?= ../ ../../../../verif
VERILATOR_DPI_DEPS := $(addprefix $(BUILD)/,$(DPI_OBJS))
VERILATOR_TB_TOP ?= $(TB)

VERILATOR_TB_FLAGS := --cc $(VERILATOR_LANG) $(addprefix -I,$(VERILATOR_INCDIRS))
VERILATOR_TB_FLAGS += --trace --trace-depth $(VERILATOR_TRACE_DEPTH)
VERILATOR_TB_FLAGS += --exe
VERILATOR_TB_FLAGS += -DN_CYCLES=$(N_CYCLES) -CFLAGS -DN_CYCLES=$(N_CYCLES)
VERILATOR_TB_FLAGS += $(addprefix -CFLAGS -I,$(VERILATOR_C_INCDIRS))
VERILATOR_TB_FLAGS += $(addprefix -LDFLAGS ,$(notdir $(VERILATOR_DPI_DEPS)))
VERILATOR_TB_FLAGS += --clk common_clk
VERILATOR_TB_FLAGS += --top-module $(VERILATOR_TB_TOP)
VERILATOR_TB_FLAGS += $(addprefix ../,$(CC_SRC))


# Verilator compile verilog into C++.
$(BUILD)/%/V$(TB).mk: $(V_SRC) $(CC_SRC) $(CC_H)
	mkdir -p $(BUILD)/$*
	verilator $(VERILATOR_TB_FLAGS) \
		--Mdir $(BUILD)/$* \
		$(call CSV_ROWMAP,$*,$(CSV_ROWMAP_CFLAGDEFINE)) \
		$(VERILATOR_TB_TOP).sv

# Compile verilated C++ into executable.
$(BUILD)/%/V$(TB): $(BUILD)/%/V$(TB).mk $(VERILATOR_DPI_DEPS)
	make -j -C $(BUILD)/$* -f V$(TB).mk V$(TB)

# Execute verilator object to dump VCD, convert to FST, then delete VCD which
# consumes unnecessary disk space.
# Then check that the data going into the queue is the same as the data coming
# out, in the same order, regardless of the time difference.
# Much simpler than a bunch of assertions for:
#   1. No data dropped.
#   2. No extraeous data inserted.
#   3. No data changed.
#   4. No data re-ordered.
# NOTE: vcd2fst comes with GtkWave.
$(BUILD)/%/$(TB).verilator.fst: $(BUILD)/%/V$(TB)
	cd $(BUILD)/$*; time ./V$(TB) > $(TB).verilator.log
	@! grep -q ERROR $(BUILD)/$*/$(TB).verilator.log
	vcd2fst $(@:.fst=.vcd) $@
	rm $(@:.fst=.vcd)
	tail -n+2 $(BUILD)/$*/pushed.log | cut -f2 -d' ' > $(BUILD)/$*/pushed.data
	tail -n+2 $(BUILD)/$*/popped.log | cut -f2 -d' ' > $(BUILD)/$*/popped.data
	diff $(BUILD)/$*/pushed.data $(BUILD)/$*/popped.data > $(BUILD)/$*/data.diff

.SECONDARY:
