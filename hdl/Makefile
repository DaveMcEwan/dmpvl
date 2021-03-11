
SRC_SINGLEHIER =
SRC_SINGLEHIER += axi4liteMonitor.sv
SRC_SINGLEHIER += binToGray.sv
SRC_SINGLEHIER += bpRegMem.sv
SRC_SINGLEHIER += corrCountRect.sv
SRC_SINGLEHIER += dividerFsm.sv
SRC_SINGLEHIER += edgeDetect.sv
SRC_SINGLEHIER += fifoW1R1.sv
SRC_SINGLEHIER += fpgaReset.sv
SRC_SINGLEHIER += fxcs.sv
SRC_SINGLEHIER += grayToBin.sv
SRC_SINGLEHIER += onehotIdx.sv
SRC_SINGLEHIER += popcnt6.sv
SRC_SINGLEHIER += prngXoroshiro128p.sv
SRC_SINGLEHIER += prngXoroshiro64s.sv
SRC_SINGLEHIER += prngXoshiro128pp.sv
SRC_SINGLEHIER += prngXoshiro128p.sv
SRC_SINGLEHIER += prngXoshiro256p.sv
SRC_SINGLEHIER += pwm.sv
SRC_SINGLEHIER += resetDetect.sv
SRC_SINGLEHIER += syncBit.sv
SRC_SINGLEHIER += usbfsEndpCtrlSerial.sv
SRC_SINGLEHIER += usbfsPktRx.sv
SRC_SINGLEHIER += usbfsPktTx.sv

SRC_MULTIHIER =
SRC_MULTIHIER += axi4liteRandomMaster.sv
SRC_MULTIHIER += axi4liteRandomSlave.sv
SRC_MULTIHIER += cdcData.sv
SRC_MULTIHIER += cdcFifo.sv
SRC_MULTIHIER += corrCountLogdrop.sv
SRC_MULTIHIER += logdropWindow.sv
SRC_MULTIHIER += mssbIdx.sv
SRC_MULTIHIER += strobe.sv
SRC_MULTIHIER += usbfsEndpRx.sv
SRC_MULTIHIER += usbfsEndpTx.sv
SRC_MULTIHIER += usbfsSerial.sv
SRC_MULTIHIER += usbfsTxn.sv
SRC_MULTIHIER += xbar.sv

# As a basic sanity check `make` should complete with no warnings or errors.
default: lint_foss
all: preproc lint_foss lint_paid

lint_foss: lint_iverilog
lint_foss: lint_verilator
lint_foss: lint_yosys

lint_paid: lint_formalpro
lint_paid: lint_jaspergold
lint_paid: lint_modelsim
lint_paid: lint_vcs
lint_paid: lint_vivado
lint_paid: lint_xmvlog

preproc: $(addprefix build/preproc/,$(SRC_MULTIHIER))
preproc: $(addprefix build/preproc/,$(SRC_SINGLEHIER))
build/preproc/%:
	mkdir -p $(shell dirname $@)
	verilator -E -P $(VERILATOR_LANG) -I. $* > $@


# RTL simulator from Steve Icarus.
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I.
lint_iverilog: lint_iverilog_singlehier
lint_iverilog: lint_iverilog_multihier
lint_iverilog_singlehier: $(addprefix lint_iverilog/,$(SRC_SINGLEHIER))
lint_iverilog_multihier:  $(addprefix lint_iverilog/,$(SRC_MULTIHIER))
lint_iverilog_singlehier/%:
	iverilog $(IVERILOG_FLAGS) $*
lint_iverilog_multihier/%:
	iverilog $(IVERILOG_FLAGS) -i $*
.PHONY: lint_iverilog lint_iverilog_singlehier lint_iverilog_multihier

# Two-state simulator via C++ from Wilson Snyder.
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I.
lint_verilator: $(addprefix lint_verilator/,$(SRC_SINGLEHIER))
lint_verilator: $(addprefix lint_verilator/,$(SRC_MULTIHIER))
lint_verilator/%:
	verilator $(VERILATOR_FLAGS) $*
.PHONY: lint_verilator

# Generic synthesis from Clifford Wolf.
lint_yosys: $(addprefix lint_yosys/,$(SRC_SINGLEHIER))
lint_yosys: $(addprefix lint_yosys/,$(SRC_MULTIHIER))
lint_yosys/%:
	yosys -q -p 'read_verilog -sv -I. $*'
.PHONY: lint_yosys


# Equivalence checker from Mentor/Siemens.
# Tested with Formalpro v2020.1
# NOTE: SYNTHESIS is defined to remove asserts using $onehot0.
FORMALPRO_LANG ?= -sv2005
FORMALPRO_FLAGS := $(FORMALPRO_LANG) +define+SYNTHESIS
lint_formalpro: $(addprefix lint_formalpro/,$(SRC_SINGLEHIER))
lint_formalpro: $(addprefix lint_formalpro/,$(SRC_MULTIHIER))
lint_formalpro/%:
	formalpro $(FORMALPRO_FLAGS) $* > /dev/null
.PHONY: lint_formalpro

# Linter from Cadence.
# Tested with HAL 20.03
# NOTE: SYNTHESIS is defined to remove asserts using $onehot0.
# NOTE: Not all warnings are removed, because some serve as useful confirmations
# about design decisions.
HAL_LANG ?= -SV
HAL_NOCHECK := LCVARN UCCONN VERCAS NUMSUF MAXLEN SEPLIN
HAL_NOCHECK += UNMGEN NBGEND NOBLKN
HAL_NOCHECK += STYVAL PRMVAL IDLENG
HAL_NOCHECK += CDWARN NOINCD
HAL_NOCHECK += DIFCLK DIFRST
HAL_NOCHECK += POOBID POIASG PRMSZM
HAL_NOCHECK += PRMBSE CONSBS CONSTC EXPIPC ATLGLC IPRTEX
HAL_NOCHECK += URDREG URDWIR
HAL_NOCHECK += ONPNSG TIELOG UNCONO DALIAS
HAL_NOCHECK += INDXOP INTTOB
HAL_NOCHECK += SYNPRT
HAL_NOCHECK += OLDALW
HAL_NOWARN := USEPRT
HAL_NOWARN += TPOUNR
HAL_NOWARN += FFWNSR FFWASR
HAL_NOWARN += VLGMEM DFDRVS
HAL_NOWARN += TRUNCZ LRGOPR RDOPND SHFTOF REVROP MULBAS IOCOMB
HAL_NOWARN += IMPDTC IMPTYP
HAL_FLAGS := $(HAL_LANG) -DATE -DEFINE SYNTHESIS
HAL_FLAGS += $(addprefix -NOCHECK ,$(HAL_NOCHECK))
HAL_FLAGS += $(addprefix -NOWARN ,$(HAL_NOWARN))
lint_hal: $(addprefix lint_hal/,$(SRC_SINGLEHIER))
lint_hal: $(addprefix lint_hal/,$(SRC_MULTIHIER))
lint_hal/%:
	hal $(HAL_FLAGS) $* \
		-LOGFILE $*.hal.log \
		-DESIGN_FACTS_FILE $*.hal.design_facts \
		> /dev/null
.PHONY: lint_hal

# Formal proof assistant from Cadence.
# Tested with JasperGold 2020.03
define JASPERGOLD_TCL
clear -all
analyze -sv05 \
	$(SRC_SINGLEHIER) \
	$(SRC_MULTIHIER)
endef
export JASPERGOLD_TCL
lint_jaspergold:
	rm -rf jgproject
	echo "$$JASPERGOLD_TCL" > jaspergold.tcl
	jaspergold -batch jaspergold.tcl > /dev/null
	@! grep -q ERROR jgproject/jg.log
.PHONY: lint_jaspergold

# RTL simulator from Intel.
# Tested with Modelsim 10.4
# NOTE: Questa is the premium edition.
MODELSIM_LANG ?= -sv05compat
MODELSIM_FLAGS := $(MODELSIM_LANG) -lint -quiet
lint_modelsim: $(addprefix lint_modelsim/,$(SRC_SINGLEHIER))
lint_modelsim: $(addprefix lint_modelsim/,$(SRC_MULTIHIER))
lint_modelsim/%:
	vlog $(MODELSIM_FLAGS) $*
	qverilog $(MODELSIM_FLAGS) $* > /dev/null
.PHONY: lint_modelsim

# RTL simulator from Mentor/Siemens.
# Tested with VCS 2018.09
VCS_LANG ?= -sverilog
VCS_FLAGS := $(VCS_LANG) +lint=all -C -q +incdir+.
lint_vcs:
	vcs $(VCS_FLAGS) $(SRC_SINGLEHIER) $(SRC_MULTIHIER) > vcs.log

# FPGA bitstream compiler from Xilinx.
# Tested with Vivado 2018.2, 2018.3
define VIVADO_TCL
create_project -in_memory projectDummy
create_fileset -blockset filesetDummy
add_files \
	$(SRC_SINGLEHIER) \
	$(SRC_MULTIHIER) \
	-fileset filesetDummy
check_syntax -fileset filesetDummy
endef
export VIVADO_TCL
lint_vivado:
	rm -f vivado_*.backup.jou
	rm -f vivado_*.backup.log
	rm -f webtalk*
	@echo "$$VIVADO_TCL" > vivado.tcl
	vivado -mode batch -source vivado.tcl > /dev/null
	@! grep -q ERROR vivado.log
	@! grep -q WARNING vivado.log
.PHONY: lint_vivado

# RTL simulator from Cadence.
# Tested with Xcelium 20.03
XMVLOG_LANG ?= -SYSV05
XMVLOG_FLAGS := $(XMVLOG_LANG) -INCDIR ./ -NOLOG
lint_xmvlog: $(addprefix lint_xmvlog/,$(SRC_SINGLEHIER))
lint_xmvlog: $(addprefix lint_xmvlog/,$(SRC_MULTIHIER))
lint_xmvlog/%:
	xmvlog $(XMVLOG_FLAGS) $* > /dev/null

.SECONDARY:
