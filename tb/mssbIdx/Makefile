
TB := mssbIdx_tb

V_SRC := \
	../../hdl/fxcs.v \
	../../hdl/onehotIdx.v \
	../../hdl/mssbIdx.v \
	$(TB).v

# NOTE: No Icarus or Verilator testbenches yet.
VCD_VERILATOR :=
#VCD_IVERILOG :=

include ../common.mk

# Check that logic evaluates as per golden reference.
yosys:
	mkdir -p $(BUILD)
	yosys -q -s mssbIdx.ys
	diff yosys.eval.txt $(BUILD)/yosys.eval.txt
