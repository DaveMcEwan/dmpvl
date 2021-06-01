
N_CYCLES ?= 7000

SRC_SINGLEHIER += ../../hdl/resetDetect.sv
SRC_SINGLEHIER += ../../hdl/prngXoroshiro128p.sv
SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/axi4liteMonitor.sv
SRC_SINGLEHIER += ../../verif/generateClock.sv

SRC_MULTIHIER += ../../hdl/axi4liteRandomSlave.sv
SRC_MULTIHIER += ../../hdl/axi4liteRandomMaster.sv

YOSYS_SRC_EXCLUDE += ../../verif/generateClock.sv

default: lint_foss
default: verilator_vcd
default: iverilog_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)

