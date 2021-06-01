
SRC_SINGLEHIER += ../../hdl/fxcs.sv

default: lint_foss
default: verilator_vcd
default: iverilog_vcd
default: yosys_equiv

MK_TB = ../../mk/tb.mk
include $(MK_TB)

# Check that logic evaluates as per golden reference.
yosys_equiv:
	mkdir -p $(BUILD)
	yosys -q -s fxcs.ys
	diff yosys.eval.mssb.txt $(BUILD)/yosys.eval.mssb.txt
	diff yosys.eval.lssb.txt $(BUILD)/yosys.eval.lssb.txt

