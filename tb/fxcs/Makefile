
TB := fxcs_tb

V_SRC := \
	../../hdl/fxcs.v \
	$(TB).v

include ../common.mk

# Check that logic evaluates as per golden reference.
yosys:
	mkdir -p $(BUILD)
	yosys -q -s fxcs.ys
	diff yosys.eval.mssb.txt $(BUILD)/yosys.eval.mssb.txt
	diff yosys.eval.lssb.txt $(BUILD)/yosys.eval.lssb.txt
