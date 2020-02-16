
TB := fifo_tb

N_CYCLES ?= 1000000

V_SRC := \
	$(TB).v \
	../../hdl/fifo.v \

CC_SRC := \
	fifo_model.cc \
	fifo_utils.cc \
	$(TB).cc

CC_H := \
	fifo_model.h \
	fifo_utils.h

# NOTE: Verilator only - no support for Icarus yet.
VCD_IVERILOG :=

include ../common.mk
