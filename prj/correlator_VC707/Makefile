
# Dave McEwan 2020-10-01


PROJ := top
BUILD := ./build

SRC := \
	../../hdl/fifo.sv \
	../../hdl/fxcs.sv \
	../../hdl/logdropWindow.sv \
	../../hdl/mssbIdx.sv \
	../../hdl/onehotIdx.sv \
	../../hdl/prngXoshiro128p.sv \
	../../hdl/strobe.sv \
	../../hdl/pwm.sv \
	../../hdl/dividerFsm.sv \
	../../hdl/corrCountRect.sv \
	../../hdl/corrCountLogdrop.sv \
	bpReg.sv \
	correlator.sv

SRC_TOP := \
	../../hdl/fpgaReset.sv \
	../../hdl/usbfsPktRx.sv \
	../../hdl/usbfsPktTx.sv \
	../../hdl/usbfsTxn.sv \
	../../hdl/usbfsEndpRx.sv \
	../../hdl/usbfsEndpTx.sv \
	../../hdl/usbfsEndpCtrlSerial.sv \
	../../hdl/usbfsSerial.sv \
	pll48.sv \
	$(PROJ).sv

default: lint synth

synth: $(BUILD)/correlator.bit

SYNTH_YOSYS ?= 0
synth_yosys: $(BUILD)/correlator.yosys.edif
%.yosys.edif: $(SRC)
	mkdir -p $(BUILD)
	yosys -q \
		-l $*.yosys.log \
		-p 'read_verilog -sv -I../../hdl/ $^' \
		-p 'synth_xilinx -top correlator -edif $*.yosys.edif' \
		-p 'flatten' \
		-p 'write_verilog $*.yosys.v'

BITFILE ?= $(BUILD)/correlator.bit
$(BITFILE): $(SRC) $(SRC_TOP) vivado.tcl vc707.xdc
ifneq ($(SYNTH_YOSYS), 0)
$(BITFILE): $(BUILD)/correlator.yosys.edif
endif
	vivado -mode batch -source vivado.tcl \
		-tclargs --synth_yosys $(SYNTH_YOSYS)

VIVADO_SIGNOFF ?= signoffVivado.regex
$(BUILD)/vivado.warnings: $(BITFILE) $(VIVADO_SIGNOFF)
	grep -n WARNING vivado.log | lineFilter $(VIVADO_SIGNOFF) > $@

signoff: $(BUILD)/vivado.warnings
	! test -s $<

# Read in design files with a variety of tools to ensure there's nothing too
# obviously wrong.
lint: lint_verilator lint_iverilog lint_yosys

VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I../../hdl
lint_verilator:
	verilator $(VERILATOR_FLAGS) bpReg.sv
	verilator $(VERILATOR_FLAGS) correlator.sv
	verilator $(VERILATOR_FLAGS) -I../../hdl/primitives/xilinx_7s pll48.sv
	verilator $(VERILATOR_FLAGS) -I../../hdl/primitives/xilinx_7s top.sv

IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I../../hdl
lint_iverilog:
	iverilog $(IVERILOG_FLAGS) -i bpReg.sv
	iverilog $(IVERILOG_FLAGS) -i correlator.sv
	iverilog $(IVERILOG_FLAGS) -i pll48.sv
	iverilog $(IVERILOG_FLAGS) -i top.sv

# pll48.sv emits warnings because the PLL primitive uses real parameters which
# yosys treats as strings.
lint_yosys:
	yosys -q -p 'read_verilog -sv -I../../hdl/ bpReg.sv'
	yosys -q -p 'read_verilog -sv -I../../hdl/ correlator.sv'
	yosys -q -p 'read_verilog -sv -I../../hdl/ top.sv'

clean:
	rm -rf build
	rm -rf .cache
	rm -rf .Xil
	rm -rf usage_statistics*
	rm -rf vivado*.log
	rm -rf vivado*.jou
	rm -rf webtalk*.log
	rm -rf webtalk*.jou

.SECONDARY:
.PHONY: default synth signoff clean
.PHONY: lint lint_verilator lint_iverilog lint_yosys
