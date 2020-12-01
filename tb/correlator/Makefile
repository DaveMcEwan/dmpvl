
TB := correlator_tb

V_SRC := \
	$(TB).sv \
	../../verif/ptyBytePipe.sv \
	../../hdl/fifoW1R1.sv \
	../../hdl/fxcs.sv \
	../../hdl/logdropWindow.sv \
	../../hdl/mssbIdx.sv \
	../../hdl/onehotIdx.sv \
	../../hdl/prngXoshiro128p.sv \
	../../hdl/strobe.sv \
	../../hdl/pwm.sv \
	../../hdl/xbar.sv \
	../../hdl/corrCountRect.sv \
	../../hdl/corrCountLogdrop.sv \
	../../prj/correlator/correlator.sv \
	../../prj/correlator/bpReg.sv \
	../../prj/correlator/bpCorrelator.sv \
	../../prj/correlator/usbfsBpCorrelator.sv

V_INCDIRS := ../../prj/correlator

CC_SRC := \
	$(TB).cc

# correlator_tb.u_correlator.u_sampleStrobe.u_prngJitter
VERILATOR_TRACE_DEPTH := 4

# NOTE: Verilator only - no support for Icarus yet.
VCD_IVERILOG :=

DPI_OBJS := ptyBytePipe.o

# Maximum runtime of 1 hour at 100Hz.
N_CYCLES := 360000

run: ./build/V$(TB)
	./run.sh
	@! grep -q ERROR ./build/run.log

include ../common.mk
