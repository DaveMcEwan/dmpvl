
# Dave McEwan 2021-03-18

# The recipies contained it this Makefile fragment are not *all* intended to
# perform linting, rather they ensure that a selection of tools can consume
# given files without doing anything too wrong.

BUILD ?= ./build
LOG_PREFIX = $(BUILD)/$(notdir $*)-
LOG_SUFFIX = -mk_lint.log

lint_foss: lint_iverilog
lint_foss: lint_verilator
lint_foss: lint_yosys

lint_paid: lint_formalpro
lint_paid: lint_hal
lint_paid: lint_jaspergold
lint_paid: lint_modelsim
lint_paid: lint_spyglass
lint_paid: lint_vcs
lint_paid: lint_vivado
lint_paid: lint_xmvlog

# RTL simulator from Steve Icarus.
IVERILOG_SRC_SINGLEHIER ?= $(filter-out $(IVERILOG_SRC_EXCLUDE),$(SRC_SINGLEHIER))
IVERILOG_SRC_MULTIHIER ?= $(filter-out $(IVERILOG_SRC_EXCLUDE),$(SRC_MULTIHIER))
IVERILOG_INCDIRS ?= $(INCDIRS)
IVERILOG_LANG ?= -g2005-sv
IVERILOG_LINT_FLAGS := $(IVERILOG_LANG) -o /dev/null $(addprefix -I,$(IVERILOG_INCDIRS))
lint_iverilog: lint_iverilog_singlehier
lint_iverilog: lint_iverilog_multihier
lint_iverilog_singlehier: $(addprefix lint_iverilog_singlehier/,$(IVERILOG_SRC_SINGLEHIER))
lint_iverilog_multihier:  $(addprefix lint_iverilog_multihier/,$(IVERILOG_SRC_MULTIHIER))
lint_iverilog_singlehier/%:
	iverilog $(IVERILOG_LINT_FLAGS) $*
lint_iverilog_multihier/%:
	iverilog $(IVERILOG_LINT_FLAGS) -i $*
.PHONY: lint_iverilog lint_iverilog_singlehier lint_iverilog_multihier

# Two-state simulator via C++ from Wilson Snyder.
VERILATOR_SRC ?= $(filter-out $(VERILATOR_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
VERILATOR_INCDIRS ?= $(INCDIRS)
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_LINT_FLAGS := $(VERILATOR_LANG) $(addprefix -I,$(VERILATOR_INCDIRS))
VERILATOR_LINT_FLAGS += --lint-only
lint_verilator: $(addprefix lint_verilator/,$(VERILATOR_SRC))
lint_verilator/%:
	verilator $(VERILATOR_LINT_FLAGS) $*
.PHONY: lint_verilator

# Generic synthesis from Clifford Wolf.
YOSYS_SRC ?= $(filter-out $(YOSYS_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
YOSYS_INCDIRS ?= $(INCDIRS)
lint_yosys: $(addprefix lint_yosys/,$(YOSYS_SRC))
lint_yosys/%:
	yosys -q -p 'read_verilog -sv $(addprefix -I,$(YOSYS_INCDIRS)) $*'
.PHONY: lint_yosys


# Equivalence checker from Mentor/Siemens.
# Tested with Formalpro v2020.1
# NOTE: SYNTHESIS is defined to remove asserts using $onehot0.
FORMALPRO_SRC ?= $(filter-out $(FORMALPRO_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
FORMALPRO_INCDIRS ?= $(INCDIRS)
FORMALPRO_LANG ?= -sv2005
FORMALPRO_LINT_FLAGS := $(FORMALPRO_LANG) +define+SYNTHESIS
FORMALPRO_LINT_FLAGS += $(addprefix +incdir+,$(FORMALPRO_INCDIRS))
FORMALPRO_LINT_LOGFILE = $(LOG_PREFIX)formalpro$(LOG_SUFFIX)
lint_formalpro: $(addprefix lint_formalpro/,$(FORMALPRO_SRC))
lint_formalpro/%:
	formalpro $(FORMALPRO_LINT_FLAGS) $* > $(FORMALPRO_LINT_LOGFILE)
.PHONY: lint_formalpro

# Linter from Cadence.
# Tested with HAL 20.03
# NOTE: SYNTHESIS is defined to remove asserts using $onehot0.
# NOTE: Not all warnings are removed, because some serve as useful confirmations
# about design decisions.
HAL_SRC ?= $(filter-out $(HAL_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
HAL_INCDIRS ?= $(INCDIRS)
HAL_LANG ?= -SV
HAL_LINT_LOGFILE = $(LOG_PREFIX)hal$(LOG_SUFFIX)
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
HAL_LINT_FLAGS := $(HAL_LANG) -DATE -DEFINE SYNTHESIS
HAL_LINT_FLAGS += $(addprefix -NOCHECK ,$(HAL_NOCHECK))
HAL_LINT_FLAGS += $(addprefix -NOWARN ,$(HAL_NOWARN))
HAL_LINT_FLAGS += $(addprefix -INCDIR ,$(HAL_INCDIRS))
HAL_LINT_FLAGS += -LOGFILE $(HAL_LINT_LOGFILE)
HAL_LINT_FLAGS += -DESIGN_FACTS_FILE $(LOG_PREFIX)hal_design_facts
lint_hal: $(addprefix lint_hal/,$(HAL_SRC))
lint_hal/%:
	mkdir -p $(BUILD)
	hal $(HAL_LINT_FLAGS) $(HAL_FLAGS) $* > /dev/null
.PHONY: lint_hal

# Formal proof assistant from Cadence.
# Tested with JasperGold 2020.03
JASPERGOLD_SRC ?= $(filter-out $(JASPERGOLD_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
JASPERGOLD_INCDIRS ?= $(INCDIRS)
#	+define+SYNTHESIS
define JASPERGOLD_TCL
clear -all
analyze -sv05 \
	$(addprefix +incdir+,$(JASPERGOLD_INCDIRS)) \
	$(JASPERGOLD_SRC)
endef
export JASPERGOLD_TCL
JASPERGOLD_TCLFILE ?= jaspergold-mk_lint.tcl
lint_jaspergold:
	rm -rf jgproject
	echo "$$JASPERGOLD_TCL" > $(JASPERGOLD_TCLFILE)
	jaspergold -batch $(JASPERGOLD_TCLFILE) > /dev/null
	@! grep -q ERROR jgproject/jg.log
.PHONY: lint_jaspergold

# RTL simulator from Mentor/Siemens.
# Tested with Modelsim 10.4
# NOTE: Questa is the premium edition.
MODELSIM_SRC ?= $(filter-out $(MODELSIM_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
MODELSIM_LANG ?= -sv05compat
MODELSIM_LINT_FLAGS := $(MODELSIM_LANG) -lint -quiet
QVERILOG_LINT_LOGFILE = $(LOG_PREFIX)qverilog$(LOG_SUFFIX)
lint_modelsim: $(addprefix lint_modelsim/,$(MODELSIM_SRC))
lint_modelsim/%:
	vlog $(MODELSIM_LINT_FLAGS) $*
	qverilog $(MODELSIM_LINT_FLAGS) $* > $(QVERILOG_LINT_LOGFILE)
.PHONY: lint_modelsim

# Linter from Synopsys.
# Tested with Spyglass 2020.12
SPYGLASS_SRC ?= $(filter-out $(SPYGLASS_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
SPYGLASS_INCDIRS ?= $(INCDIRS)
define SPYGLASS_TCL
set_option enableSV yes
set_option incdir $(SPYGLASS_INCDIRS)
read_file $(SPYGLASS_SRC)
endef
export SPYGLASS_TCL
SPYGLASS_TCLFILE ?= $(BUILD)/spyglass-mk_lint.prj
SPYGLASS_LINT_LOGFILE = $(BUILD)/spyglass$(LOG_SUFFIX)
lint_spyglass:
	mkdir -p $(BUILD)
	@echo "$$SPYGLASS_TCL" > $(SPYGLASS_TCLFILE)
	spyglass -batch -designread -project $(SPYGLASS_TCLFILE) > $(SPYGLASS_LINT_LOGFILE)
.PHONY: lint_spyglass

# RTL simulator from Synopsys.
# Tested with VCS 2018.09
VCS_SRC ?= $(filter-out $(VCS_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
VCS_INCDIRS ?= $(INCDIRS)
VCS_LANG ?= -sverilog
VCS_LINT_FLAGS := $(VCS_LANG) +lint=all -C -q $(addprefix +incdir+,$(VCS_INCDIRS))
VCS_LINT_LOGFILE ?= $(BUILD)/vcs-mk_lint.log
lint_vcs:
	mkdir -p $(BUILD)
	vcs $(VCS_LINT_FLAGS) $(VCS_SRC) > $(VCS_LINT_LOGFILE)

# FPGA bitstream compiler from Xilinx.
# Tested with Vivado 2018.2, 2018.3
VIVADO_SRC ?= $(filter-out $(VIVADO_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
define VIVADO_TCL
create_project -in_memory projectDummy
create_fileset -blockset filesetDummy
add_files $(VIVADO_SRC) -fileset filesetDummy
check_syntax -fileset filesetDummy
endef
export VIVADO_TCL
VIVADO_TCLFILE ?= $(BUILD)/vivado-mk_lint.tcl
VIVADO_LINT_LOGFILE = $(BUILD)/vivado$(LOG_SUFFIX)
lint_vivado:
	rm -f vivado*.jou
	rm -f vivado*.log
	rm -f webtalk*
	mkdir -p $(BUILD)
	@echo "$$VIVADO_TCL" > $(VIVADO_TCLFILE)
	vivado -mode batch -source $(VIVADO_TCLFILE) > /dev/null
	mv vivado.log $(VIVADO_LINT_LOGFILE)
	! grep -q ERROR $(VIVADO_LINT_LOGFILE)
	! grep -q WARNING $(VIVADO_LINT_LOGFILE)
.PHONY: lint_vivado

# RTL simulator from Cadence, successor to Incisive.
# Tested with Xcelium 20.03
XMVLOG_SRC ?= $(filter-out $(XMVLOG_SRC_EXCLUDE),$(SRC_SINGLEHIER) $(SRC_MULTIHIER))
XMVLOG_INCDIRS ?= $(INCDIRS)
XMVLOG_LANG ?= -SYSV05
XMVLOG_LINT_FLAGS := $(XMVLOG_LANG) -NOLOG $(addprefix -INCDIR ,$(XMVLOG_INCDIRS))
XMVLOG_LINT_LOGFILE = $(LOG_PREFIX)xmvlog$(LOG_SUFFIX)
lint_xmvlog: $(addprefix lint_xmvlog/,$(XMVLOG_SRC))
lint_xmvlog/%:
	mkdir -p $(BUILD)
	xmvlog $(XMVLOG_LINT_FLAGS) $* > $(XMVLOG_LINT_LOGFILE)


CLEAN_PATHS += work
CLEAN_PATHS += jgproject
CLEAN_PATHS += .Xil
CLEAN_PATHS += vivado*.log
CLEAN_PATHS += vivado*.jou
CLEAN_PATHS += *-mk_lint.*

.SECONDARY:
