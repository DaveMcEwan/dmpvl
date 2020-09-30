
TB := bpRegMem_tb

N_CYCLES ?= 1000000

V_SRC := \
	$(TB).sv \
	../../verif/generateClock.sv \
	../../hdl/bpRegMem.sv

CC_SRC := \
	bpRegMem_model.cc \
	../../verif/modelPrint.cc \
	$(TB).cc

CC_H := \
	bpRegMem_model.h \
	../../verif/modelPrint.h

# NOTE: Verilator only - no checking support for Icarus yet.
#VCD_IVERILOG :=

include ../common.mk
