
# Dave McEwan 2021-03-18

# The recipies contained it this Makefile fragment are not *all* intended to
# perform linting, rather they ensure that a selection of tools can consume
# given files without doing anything too wrong.

BUILD ?= ./build
LOG_PREFIX = $(BUILD)/$(notdir $*)-
LOG_SUFFIX = -lint_mk.log

lint_foss: lint_iverilog
lint_foss: lint_verilator
lint_foss: lint_yosys

lint_paid: lint_formalpro
lint_paid: lint_jaspergold
lint_paid: lint_hal
lint_paid: lint_modelsim
lint_paid: lint_spyglass
lint_paid: lint_vcs
lint_paid: lint_vivado
lint_paid: lint_xmvlog

# RTL simulator from Steve Icarus.
IVERILOG_SRC_SINGLEHIER ?= $(SRC_SINGLEHIER)
IVERILOG_SRC_MULTIHIER ?= $(SRC_MULTIHIER)
IVERILOG_INCDIRS ?= $(INCDIRS)
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null $(addprefix -I,$(IVERILOG_INCDIRS))
lint_iverilog: lint_iverilog_singlehier
lint_iverilog: lint_iverilog_multihier
lint_iverilog_singlehier: $(addprefix lint_iverilog_singlehier/,$(IVERILOG_SRC_SINGLEHIER))
lint_iverilog_multihier:  $(addprefix lint_iverilog_multihier/,$(IVERILOG_SRC_MULTIHIER))
lint_iverilog_singlehier/%:
	iverilog $(IVERILOG_FLAGS) $*
lint_iverilog_multihier/%:
	iverilog $(IVERILOG_FLAGS) -i $*
.PHONY: lint_iverilog lint_iverilog_singlehier lint_iverilog_multihier

# Two-state simulator via C++ from Wilson Snyder.
VERILATOR_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
VERILATOR_INCDIRS ?= $(INCDIRS)
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := $(VERILATOR_LANG) $(addprefix -I,$(VERILATOR_INCDIRS))
lint_verilator: $(addprefix lint_verilator/,$(VERILATOR_SRC))
lint_verilator/%:
	verilator --lint-only $(VERILATOR_FLAGS) $*
.PHONY: lint_verilator

# Generic synthesis from Clifford Wolf.
YOSYS_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
YOSYS_INCDIRS ?= $(INCDIRS)
lint_yosys: $(addprefix lint_yosys/,$(YOSYS_SRC))
lint_yosys/%:
	yosys -q -p 'read_verilog -sv $(addprefix -I,$(YOSYS_INCDIRS)) $*'
.PHONY: lint_yosys


# Equivalence checker from Mentor/Siemens.
# Tested with Formalpro v2020.1
# NOTE: SYNTHESIS is defined to remove asserts using $onehot0.
FORMALPRO_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
FORMALPRO_INCDIRS ?= $(INCDIRS)
FORMALPRO_LANG ?= -sv2005
FORMALPRO_FLAGS := $(FORMALPRO_LANG) +define+SYNTHESIS
FORMALPRO_FLAGS += $(addprefix +incdir+,$(FORMALPRO_INCDIRS))
FORMALPRO_LOGFILE = $(LOG_PREFIX)formalpro$(LOG_SUFFIX)
lint_formalpro: $(addprefix lint_formalpro/,$(FORMALPRO_SRC))
lint_formalpro/%:
	formalpro $(FORMALPRO_FLAGS) $* > $(FORMALPRO_LOGFILE)
.PHONY: lint_formalpro

# Linter from Cadence.
# Tested with HAL 20.03
# NOTE: SYNTHESIS is defined to remove asserts using $onehot0.
# NOTE: Not all warnings are removed, because some serve as useful confirmations
# about design decisions.
HAL_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
HAL_INCDIRS ?= $(INCDIRS)
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
HAL_FLAGS += $(addprefix -INCDIR ,$(HAL_INCDIRS))
HAL_LOGFILE = $(LOG_PREFIX)hal$(LOG_SUFFIX)
lint_hal: $(addprefix lint_hal/,$(HAL_SRC))
lint_hal/%:
	mkdir -p $(BUILD)
	hal $(HAL_FLAGS) $* \
		-LOGFILE $(HAL_LOGFILE) \
		-DESIGN_FACTS_FILE $(LOG_PREFIX)hal_design_facts \
		> /dev/null
.PHONY: lint_hal

# Formal proof assistant from Cadence.
# Tested with JasperGold 2020.03
JASPERGOLD_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
JASPERGOLD_INCDIRS ?= $(INCDIRS)
define JASPERGOLD_TCL
clear -all
analyze -sv05 \
	$(addprefix +incdir+,$(JASPERGOLD_INCDIRS)) \
	$(JASPERGOLD_SRC)
endef
export JASPERGOLD_TCL
JASPERGOLD_TCLFILE ?= jaspergold-lint_mk.tcl
lint_jaspergold:
	rm -rf jgproject
	echo "$$JASPERGOLD_TCL" > $(JASPERGOLD_TCLFILE)
	jaspergold -batch $(JASPERGOLD_TCLFILE) > /dev/null
	@! grep -q ERROR jgproject/jg.log
.PHONY: lint_jaspergold

# RTL simulator from Mentor/Siemens.
# Tested with Modelsim 10.4
# NOTE: Questa is the premium edition.
MODELSIM_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
MODELSIM_LANG ?= -sv05compat
MODELSIM_FLAGS := $(MODELSIM_LANG) -lint -quiet
QVERILOG_LOGFILE = $(LOG_PREFIX)qverilog$(LOG_SUFFIX)
lint_modelsim: $(addprefix lint_modelsim/,$(MODELSIM_SRC))
lint_modelsim/%:
	vlog $(MODELSIM_FLAGS) $*
	qverilog $(MODELSIM_FLAGS) $* > $(QVERILOG_LOGFILE)
.PHONY: lint_modelsim

# Linter from Synopsys.
# Tested with Spyglass 2020.12
SPYGLASS_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
SPYGLASS_INCDIRS ?= $(INCDIRS)
define SPYGLASS_TCL
set_option enableSV yes
set_option incdir $(SPYGLASS_INCDIRS)
read_file $(SPYGLASS_SRC)
endef
export SPYGLASS_TCL
SPYGLASS_TCLFILE ?= $(BUILD)/spyglass-lint_mk.prj
SPYGLASS_LOGFILE = $(BUILD)/spyglass$(LOG_SUFFIX)
lint_spyglass:
	mkdir -p $(BUILD)
	@echo "$$SPYGLASS_TCL" > $(SPYGLASS_TCLFILE)
	spyglass -batch -designread -project $(SPYGLASS_TCLFILE) > $(SPYGLASS_LOGFILE)
.PHONY: lint_spyglass

# RTL simulator from Synopsys.
# Tested with VCS 2018.09
VCS_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
VCS_INCDIRS ?= $(INCDIRS)
VCS_LANG ?= -sverilog
VCS_FLAGS := $(VCS_LANG) +lint=all -C -q $(addprefix +incdir+,$(VCS_INCDIRS))
VCS_LOGFILE ?= $(BUILD)/vcs-lint_mk.tcl
lint_vcs:
	mkdir -p $(BUILD)
	vcs $(VCS_FLAGS) $(VCS_SRC) > $(VCS_LOGFILE)

# FPGA bitstream compiler from Xilinx.
# Tested with Vivado 2018.2, 2018.3
VIVADO_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
define VIVADO_TCL
create_project -in_memory projectDummy
create_fileset -blockset filesetDummy
add_files $(VIVADO_SRC) -fileset filesetDummy
check_syntax -fileset filesetDummy
endef
export VIVADO_TCL
VIVADO_TCLFILE ?= $(BUILD)/vivado-lint_mk.tcl
VIVADO_LOGFILE = $(BUILD)/vivado$(LOG_SUFFIX)
lint_vivado:
	rm -f vivado*.jou
	rm -f vivado*.log
	rm -f webtalk*
	mkdir -p $(BUILD)
	@echo "$$VIVADO_TCL" > $(VIVADO_TCLFILE)
	vivado -mode batch -source $(VIVADO_TCLFILE) > /dev/null
	mv vivado.log $(VIVADO_LOGFILE)
	! grep -q ERROR $(VIVADO_LOGFILE)
	! grep -q WARNING $(VIVADO_LOGFILE)
.PHONY: lint_vivado

# RTL simulator from Cadence, successor to Incisive.
# Tested with Xcelium 20.03
XMVLOG_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
XMVLOG_INCDIRS ?= $(INCDIRS)
XMVLOG_LANG ?= -SYSV05
XMVLOG_FLAGS := $(XMVLOG_LANG) -NOLOG $(addprefix -INCDIR ,$(XMVLOG_INCDIRS))
XMVLOG_LOGFILE = $(LOG_PREFIX)xmvlog$(LOG_SUFFIX)
lint_xmvlog: $(addprefix lint_xmvlog/,$(XMVLOG_SRC))
lint_xmvlog/%:
	mkdir -p $(BUILD)
	xmvlog $(XMVLOG_FLAGS) $* > $(XMVLOG_LOGFILE)

.SECONDARY:
