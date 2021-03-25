
N_CYCLES ?= 1000000

SRC_SINGLEHIER += ../../hdl/bpRegMem.sv
SRC_SINGLEHIER += ../../verif/generateClock.sv

YOSYS_SRC_EXCLUDE += ../../verif/generateClock.sv
YOSYS_SRC_EXCLUDE += bpRegMem_tb.sv

CC_SRC += bpRegMem_model.cc
CC_SRC += ../../verif/modelPrint.cc

CC_H += bpRegMem_model.h
CC_H += ../../verif/modelPrint.h

default: lint_foss
default: verilator_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)
