
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
all: lint_foss lint_vivado

lint_foss: lint_verilator
lint_foss: lint_iverilog
lint_foss: lint_yosys

VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I.
lint_verilator: $(addprefix lint_verilator/,$(SRC_SINGLEHIER))
lint_verilator: $(addprefix lint_verilator/,$(SRC_MULTIHIER))
lint_verilator/%:
	verilator $(VERILATOR_FLAGS) $*

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

lint_yosys: $(addprefix lint_yosys/,$(SRC_SINGLEHIER))
lint_yosys: $(addprefix lint_yosys/,$(SRC_MULTIHIER))
lint_yosys/%:
	yosys -q -p 'read_verilog -sv -I. $*'

.PHONY: lint_foss lint_verilator lint_iverilog lint_yosys
.PHONY: lint_iverilog_singlehier lint_iverilog_multihier

preproc: $(addprefix build/preproc/,$(SRC_MULTIHIER))
preproc: $(addprefix build/preproc/,$(SRC_SINGLEHIER))
build/preproc/%:
	mkdir -p $(shell dirname $@)
	verilator -E -P $(VERILATOR_LANG) -I. $* > $@


# Tested with Vivado 2018.2
define VIVADO_TCL =
create_project -in_memory projectDummy
create_fileset -blockset filesetDummy
add_files \\
	$(SRC_SINGLEHIER) \\
	$(SRC_MULTIHIER) \\
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

.SECONDARY:
