
BUILD ?= ./build

PREPROC_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)

VERILATOR_INCDIRS ?= $(INCDIRS)
VERILATOR_LANG ?= --language 1800-2005
preproc: $(addprefix $(BUILD)/preproc/,$(PREPROC_SRC))
$(BUILD)/preproc/%:
	mkdir -p $(shell dirname $@)
	verilator -E -P $(VERILATOR_LANG) $(addprefix -I,$(VERILATOR_INCDIRS)) $* \
		> $(BUILD)/preproc/$(notdir $*)

