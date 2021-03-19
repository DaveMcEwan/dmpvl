
BUILD ?= ./build

PREPROC_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)

VERILATOR_INCDIRS ?= $(INCDIRS)
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_PREPROC_FLAGS := $(VERILATOR_LANG) $(addprefix -I,$(VERILATOR_INCDIRS))
VERILATOR_PREPROC_FLAGS += -E -P -Mdir $(BUILD)/obj_dir

preproc: $(addprefix $(BUILD)/preproc/,$(PREPROC_SRC))
$(BUILD)/preproc/%:
	mkdir -p $(shell dirname $@)
	verilator $(VERILATOR_PREPROC_FLAGS) $* > $(BUILD)/preproc/$(notdir $*)

