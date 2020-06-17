
TB := correlator_tb

V_SRC := \
	$(TB).v \
	../../verif/ptyBytePipe.v \
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
	$(TB).cc

# NOTE: Verilator only - no support for Icarus yet.
VCD_IVERILOG :=

DPI_OBJS := ptyBytePipe.o

# Maximum runtime of 1 hour at 100Hz.
N_CYCLES := 360000

run: ./build/V$(TB)
	./run.sh
	@! grep -q ERROR ./build/run.log

include ../common.mk
