
N_CYCLES ?= 1000000

SRC_SINGLEHIER += ../../verif/generateClock.sv
SRC_SINGLEHIER += ../../hdl/dividerFsm.sv

YOSYS_SRC_EXCLUDE += ../../verif/generateClock.sv
YOSYS_SRC_EXCLUDE += dividerFsm_tb.sv

default: lint_foss
default: verilator_vcd
default: iverilog_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)

