
# Dave McEwan 2020-10-01

PRJ ?= correlator
BUILD := ./build

# AC701 (Artix-7)             xc7a200tfbg676-2
# KC705 (Kintex-7)            xc7k325tffg900-2
# KCU1500 (Kintex UltraScale) xcku115-flvb2104-2-e
# KCU116 (Kintex UltraScale+) xcku5p-ffvb676-2-e
# VC707 (Virtex-7)            xc7vx485tffg1157-1, xc7vx485tffg1761-2
# VCU108 (Virtex UltraScale)  xcvu095-ffva2104-2-e
# VCU118 (Virtex UltraScale+) xcvu9p-flga2104-2L-e
# ZC702,Zedboard (Zynq)       xc7z020clg484-1
# ZCU102 (Zynq UltraScale+)   xczu9eg-ffvb1156-2-i
PART := xc7z020clg484-1

default: lint_foss
default: signoff

SRC_SINGLEHIER += ../../hdl/corrCountRect.sv
SRC_SINGLEHIER += ../../hdl/dividerFsm.sv
SRC_SINGLEHIER += ../../hdl/fifoW1R1.sv
SRC_SINGLEHIER += ../../hdl/fpgaReset.sv
SRC_SINGLEHIER += ../../hdl/fxcs.sv
SRC_SINGLEHIER += ../../hdl/onehotIdx.sv
SRC_SINGLEHIER += ../../hdl/popcnt6.sv
SRC_SINGLEHIER += ../../hdl/prngXoshiro128p.sv
SRC_SINGLEHIER += ../../hdl/pwm.sv
SRC_SINGLEHIER += ../../hdl/usbfsEndpCtrlSerial.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktRx.sv
SRC_SINGLEHIER += ../../hdl/usbfsPktTx.sv

SRC_MULTIHIER += ../../hdl/corrCountLogdrop.sv
SRC_MULTIHIER += ../../hdl/logdropWindow.sv
SRC_MULTIHIER += ../../hdl/mssbIdx.sv
SRC_MULTIHIER += ../../hdl/strobe.sv
SRC_MULTIHIER += ../../hdl/usbfsEndpRx.sv
SRC_MULTIHIER += ../../hdl/usbfsEndpTx.sv
SRC_MULTIHIER += ../../hdl/usbfsSerial.sv
SRC_MULTIHIER += ../../hdl/usbfsTxn.sv
SRC_MULTIHIER += ../../hdl/xbar.sv
SRC_MULTIHIER += correlator.sv
SRC_MULTIHIER += bpReg.sv
SRC_MULTIHIER += bpCorrelator.sv
SRC_MULTIHIER += usbfsBpCorrelator.sv
SRC_MULTIHIER += pll48.sv
SRC_MULTIHIER += top.sv

SRC_COMBINED := $(SRC_SINGLEHIER) $(SRC_MULTIHIER)

INCDIRS = . ../../hdl

VERILATOR_SRC			?= $(subst top.sv,,$(SRC_COMBINED))
VERILATOR_INCDIRS := $(INCDIRS) ../../hdl/primitives/xilinx_7s
VCS_SRC       ?= $(subst top.sv,,$(SRC_COMBINED))
YOSYS_SRC     ?= $(subst pll48.sv,,$(SRC_COMBINED))
MK_LINT := ../../mk/lint.mk
include $(MK_LINT)

MK_PREPROC := ../../mk/preproc.mk
include $(MK_PREPROC)

YOSYS_TOP ?= usbfsBpCorrelator
MK_XILINX7S := ../../mk/xilinx7s.mk
include $(MK_XILINX7S)

MK_CLEAN := ../../mk/clean.mk
include $(MK_CLEAN)

