
N_CYCLES ?= 2000

SRC_SINGLEHIER += ../../hdl/syncBit.sv
SRC_SINGLEHIER += ../../hdl/pwm.sv
SRC_SINGLEHIER += ../../verif/generateClock.sv

default: lint_foss
default: verilator_vcd
default: iverilog_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)
