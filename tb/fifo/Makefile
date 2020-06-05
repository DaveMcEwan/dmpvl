
TB := fifo_tb

N_CYCLES ?= 1000000

V_SRC := \
	$(TB).v \
	../../hdl/fifo.v

CC_SRC := \
	fifo_model.cc \
	../../verif/modelPrint.cc \
	$(TB).cc

CC_H := \
	fifo_model.h \
	../../verif/modelPrint.h

# NOTE: Verilator only - no support for Icarus yet.
VCD_IVERILOG :=

include ../common.mk
