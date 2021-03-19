
clean: $(addprefix clean/,$(CLEAN_PATHS))
clean/%:
	rm -rf $*
.PHONY: clean

