
SRC_SINGLEHIER += ../../hdl/fxcs.sv
SRC_SINGLEHIER += ../../hdl/onehotIdx.sv

SRC_MULTIHIER += ../../hdl/mssbIdx.sv

default: lint_foss
default: verilator_vcd
default: yosys_equiv

MK_TB = ../../mk/tb.mk
include $(MK_TB)

# Check that logic evaluates as per golden reference.
yosys_equiv:
	mkdir -p $(BUILD)
	yosys -q -s mssbIdx.ys
	diff yosys.eval.txt $(BUILD)/yosys.eval.txt

