
N_CYCLES ?= 1000000

SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv

CC_SRC += ../../verif/modelPrint.cc
CC_SRC += fifo_model.cc

CC_H += ../../verif/modelPrint.h
CC_H += fifo_model.h

default: lint_foss
default: verilator_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)

