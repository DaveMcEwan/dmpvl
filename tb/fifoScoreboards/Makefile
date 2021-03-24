
TB := fifoScoreboards_tb

N_CYCLES ?= 1000000

BUILD ?= ./build

MK_CSV = ../../mk/csv.mk
include $(MK_CSV)

ALL_TB_VERILATOR_VCD := $(addprefix $(BUILD)/,$(addsuffix /$(TB).verilator.fst,$(CSV_ROWS)))
ALL_TB_IVERILOG_VCD := #$(addprefix $(BUILD)/,$(addsuffix /$(TB).iverilog.fst,$(CSV_ROWS)))
.PHONY: all
all: $(ALL_TB_VERILATOR_VCD) $(ALL_TB_IVERILOG_VCD)
	@echo $(TB) PASSED

V_SRC := \
	$(TB).sv \
	../../hdl/binToGray.sv \
	../../hdl/grayToBin.sv \
	../../hdl/cdcData.sv \
	../../hdl/cdcFifo.sv \
	../../hdl/fifoW1R1.sv

CC_SRC := \
	../../verif/modelPrint.cc \
	$(TB).cc

CC_H := \
	../../verif/modelPrint.h

V_INCDIRS := ../../hdl ../../verif
VERILATOR_INCDIRS := $(addprefix -I,$(V_INCDIRS))

# Verilator compile verilog into C++.
VERILATOR_TOP ?= $(TB)
VERILATOR_TRACE_DEPTH ?= 3
$(BUILD)/%/V$(TB).mk: $(V_SRC) $(CC_SRC) $(CC_H)
	mkdir -p $(BUILD)/$*
	verilator --cc \
		--trace \
		--trace-depth $(VERILATOR_TRACE_DEPTH) \
		--exe \
		$(VERILATOR_INCDIRS) \
		--Mdir $(BUILD)/$* \
		$(call CSV_ROWMAP,$*,$(CSV_ROWMAP_CFLAGDEFINE)) \
		-DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -I../../../../verif \
		$(VERILATOR_DPI_OBJS) \
		--clk common_clk \
		--top-module $(VERILATOR_TOP) \
		$(addprefix ../,$(CC_SRC)) \
		$(VERILATOR_TOP).sv

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


.PHONY: clean
clean:
	rm -rf $(BUILD)

.SECONDARY:
