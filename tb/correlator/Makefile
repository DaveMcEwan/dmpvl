
# Maximum runtime of 1 hour at 100Hz.
N_CYCLES := 360000

# correlator_tb.u_correlator.u_sampleStrobe.u_prngJitter
VERILATOR_TRACE_DEPTH := 4

SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/fxcs.sv
SRC_SINGLEHIER += ../../hdl/onehotIdx.sv
SRC_SINGLEHIER += ../../hdl/prngXoshiro128p.sv
SRC_SINGLEHIER += ../../hdl/pwm.sv
SRC_SINGLEHIER += ../../hdl/xbar.sv
SRC_SINGLEHIER += ../../hdl/corrCountRect.sv
SRC_SINGLEHIER += ../../hdl/fxcs.sv
SRC_SINGLEHIER += ../../prj/correlator/bpReg.sv
SRC_SINGLEHIER += ../../verif/ptyBytePipe.sv

SRC_MULTIHIER += ../../hdl/mssbIdx.sv
SRC_MULTIHIER += ../../hdl/logdropWindow.sv
SRC_MULTIHIER += ../../hdl/strobe.sv
SRC_MULTIHIER += ../../hdl/corrCountLogdrop.sv
SRC_MULTIHIER += ../../prj/correlator/correlator.sv
SRC_MULTIHIER += ../../prj/correlator/bpCorrelator.sv
SRC_MULTIHIER += ../../prj/correlator/usbfsBpCorrelator.sv

INCDIRS ?= . ../../hdl ../../verif ../../prj/correlator

YOSYS_SRC_EXCLUDE += ../../verif/ptyBytePipe.sv
IVERILOG_SRC_EXCLUDE += ../../verif/ptyBytePipe.sv

DPI_OBJS := ptyBytePipe.o

default: lint_foss
default: verilator_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)

run: ./build/V$(TB)
	./run.sh
	@! grep -q ERROR ./build/run.log

