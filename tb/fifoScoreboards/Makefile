
TB := fifoScoreboards_tb

N_CYCLES ?= 1000000

BUILD ?= ./build

space :=
space +=
CSV_KEYS = $(strip        DUT_TYPE  WIDTH  DEPTH  FLOPS_NOT_MEM   TOPOLOGY  FORCEKEEP_NENTRIES  CDC)
CSV :=
CSV += $(subst $(space),,fifoW1R1, 1,     8,     0,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 2,     8,     0,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 5,     8,     0,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     8,     0,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 1,     8,     1,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 2,     8,     1,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 5,     8,     1,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     8,     1,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     2,     0,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     3,     0,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     4,     0,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     5,     0,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     2,     1,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     3,     1,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     4,     1,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     5,     1,              0,        0,                  0)
CSV += $(subst $(space),,fifoW1R1, 8,     8,     0,              0,        1,                  0)

CSV += $(subst $(space),,cdcFifo,  8,     8,     0,              0,        0,                  0)
CSV += $(subst $(space),,cdcFifo,  8,     8,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  5,     8,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  2,     8,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  1,     8,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  8,     4,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  8,     2,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  8,     8,     1,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  5,     8,     1,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  2,     8,     1,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  1,     8,     1,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  8,     4,     1,              0,        0,                  1)
CSV += $(subst $(space),,cdcFifo,  8,     2,     1,              0,        0,                  1)
#CSV += $(subst $(space),,cdcFifo,  8,     8,     0,              1,        0,                  0)
#CSV += $(subst $(space),,cdcFifo,  8,     8,     0,              1,        0,                  1)

CSV += $(subst $(space),,cdcData,  8,     2,     0,              0,        0,                  0)
CSV += $(subst $(space),,cdcData,  8,     2,     0,              1,        0,                  0)
CSV += $(subst $(space),,cdcData,  1,     2,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcData,  2,     2,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcData,  5,     2,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcData,  8,     2,     0,              0,        0,                  1)
CSV += $(subst $(space),,cdcData,  1,     2,     1,              0,        0,                  1)
CSV += $(subst $(space),,cdcData,  2,     2,     1,              0,        0,                  1)
CSV += $(subst $(space),,cdcData,  5,     2,     1,              0,        0,                  1)
CSV += $(subst $(space),,cdcData,  8,     2,     1,              0,        0,                  1)
CSV += $(subst $(space),,cdcData,  1,     2,     0,              1,        0,                  1)
CSV += $(subst $(space),,cdcData,  2,     2,     0,              1,        0,                  1)
CSV += $(subst $(space),,cdcData,  5,     2,     0,              1,        0,                  1)
CSV += $(subst $(space),,cdcData,  8,     2,     0,              1,        0,                  1)
CSV += $(subst $(space),,cdcData,  1,     2,     1,              1,        0,                  1)
CSV += $(subst $(space),,cdcData,  2,     2,     1,              1,        0,                  1)
CSV += $(subst $(space),,cdcData,  5,     2,     1,              1,        0,                  1)
CSV += $(subst $(space),,cdcData,  8,     2,     1,              1,        0,                  1)

N_CSV_KEYS := $(shell echo $(CSV_KEYS) | wc -w)
CSV_MAP = \
	for i in $$(seq 1 $(N_CSV_KEYS)); do \
		KEY=$$(echo $(CSV_KEYS) | cut -d' ' -f$$i); \
		VALUE=$$(echo $* | cut -d',' -f$$i); \
		echo -D$$KEY=$$VALUE; \
  done

TB_VERILATOR_VCD = $(BUILD)/$(ROW)/$(TB).verilator.fst
TB_IVERILOG_VCD = $(BUILD)/$(ROW)/$(TB).iverilog.fst
ALL_TB_VERILATOR_VCD := $(foreach ROW,$(CSV),$(TB_VERILATOR_VCD))
ALL_TB_IVERILOG_VCD := #$(foreach ROW,$(CSV),$(TB_IVERILOG_VCD))
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
		$(shell $(CSV_MAP)) \
		-DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -DN_CYCLES=$(N_CYCLES) \
		-CFLAGS -I../../../../verif \
		$(VERILATOR_DPI_OBJS) \
		--clk common_clk \
		--top-module $(VERILATOR_TOP) \
		$(foreach src,$(CC_SRC),../$(src)) \
		$(VERILATOR_TOP).sv

# Compile verilated C++ into executable.
$(BUILD)/%/V$(TB): $(BUILD)/%/V$(TB).mk $(VERILATOR_DPI_DEPS)
	make -j -C $(BUILD)/$* -f V$(TB).mk V$(TB)

# Execute verilator object to dump VCD.
# Then check that the data going into the queue is the same as the data coming
# out, in the same order, regardless of the time difference.
# Much simpler than a bunch of assertions for:
#   1. No data dropped.
#   2. No extraeous data inserted.
#   3. No data changed.
#   4. No data re-ordered.
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
