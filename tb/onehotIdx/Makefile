
SRC_SINGLEHIER += ../../hdl/onehotIdx.sv

default: lint_foss
default: verilator_vcd
default: iverilog_vcd
default: yosys_equiv

MK_TB = ../../mk/tb.mk
include $(MK_TB)

# Check that logic evaluates as per golden reference.
yosys_equiv:
	mkdir -p $(BUILD)
	yosys -q -s onehotIdx.ys
	diff yosys.eval.txt $(BUILD)/yosys.eval.txt

