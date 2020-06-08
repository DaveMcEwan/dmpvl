
TB := correlator_tb

N_CYCLES ?= 1000000

V_SRC := \
	$(TB).v \
	../../hdl/fifo.v \
	../../hdl/fxcs.v \
	../../hdl/logdropWindow.v \
	../../hdl/mssbIdx.v \
	../../hdl/onehotIdx.v \
	../../hdl/prngXoshiro128p.v \
	../../hdl/strobe.v \
	../../prj/correlator/corrCountRect.v \
	../../prj/correlator/corrCountLogdrop.v \
	../../prj/correlator/bpReg.v \
	../../prj/correlator/correlator.v

V_INCDIRS := ../../prj/correlator

CC_SRC := \
	../../verif/ptyBytePipe.c \
	$(TB).cc

CC_H := \
	../../verif/ptyBytePipe.h

# NOTE: Verilator only - no support for Icarus yet.
VCD_IVERILOG :=

include ../common.mk
