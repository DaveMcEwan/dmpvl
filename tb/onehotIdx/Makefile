
TB := onehotIdx_tb

V_SRC := \
	../../hdl/onehotIdx.sv \
	$(TB).sv

include ../common.mk

# Check that logic evaluates as per golden reference.
yosys:
	mkdir -p $(BUILD)
	yosys -q -s onehotIdx.ys
	diff yosys.eval.txt $(BUILD)/yosys.eval.txt
