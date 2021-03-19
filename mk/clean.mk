
BUILD ?= ./build

CLEAN_PATHS += $(BUILD)

clean: $(addprefix clean/,$(CLEAN_PATHS))
clean/%:
	rm -rf $*
.PHONY: clean

