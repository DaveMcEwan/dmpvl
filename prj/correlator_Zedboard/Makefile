
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
	../../hdl/xbar.sv \
	../../hdl/usbfsPktRx.sv \
	../../hdl/usbfsPktTx.sv \
	../../hdl/usbfsTxn.sv \
	../../hdl/usbfsEndpRx.sv \
	../../hdl/usbfsEndpTx.sv \
	../../hdl/usbfsEndpCtrlSerial.sv \
	../../hdl/usbfsSerial.sv \
	bpReg.sv \
	correlator.sv \
	bpCorrelator.sv \
	usbfsBpCorrelator.sv

SRC_TOP := \
	../../hdl/fpgaReset.sv \
	pll48.sv \
	top.sv

default: lint signoff


SYNTH_YOSYS ?= 0
synth_yosys: $(BUILD)/usbfsBpCorrelator.edif
%.edif: $(SRC)
	mkdir -p $(BUILD)
	yosys -q \
		-l $*.yosys.log \
		-p 'read_verilog -sv -I../../hdl/ $^' \
		-p 'synth_xilinx -top usbfsBpCorrelator -edif $*.edif' \
		-p 'flatten' \
		-p 'write_verilog $*.yosys.v'

BITFILE ?= $(BUILD)/$(PRJ).bit
$(BITFILE): $(SRC) $(SRC_TOP) vivado.tcl zedboard_master_XDC_RevC_D_v3.xdc
ifneq ($(SYNTH_YOSYS), 0)
$(BITFILE): $(BUILD)/usbfsBpCorrelator.edif
endif
	vivado -mode batch -source vivado.tcl \
		-tclargs --prj $(PRJ) --part $(PART) --dirBuild $(BUILD) \
			--synth_yosys $(SYNTH_YOSYS)

synth: $(BITFILE)


VIVADO_SIGNOFF ?= signoffVivado.regex
$(BUILD)/vivado.warnings: $(BITFILE) $(VIVADO_SIGNOFF)
	grep -n WARNING vivado.log | lineFilter $(VIVADO_SIGNOFF) > $@

signoff: $(BUILD)/vivado.warnings
	! test -s $<


prog: signoff
	vivado -mode batch -source ../../tcl/vivado-program.tcl \
		-tclargs --part xc7z020clg484-1 --bitstream $(BITFILE)


# Read in design files with a variety of tools to ensure there's nothing too
# obviously wrong.
lint: lint_verilator lint_iverilog lint_yosys

VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I../../hdl
lint_verilator:
	verilator $(VERILATOR_FLAGS) correlator.sv
	verilator $(VERILATOR_FLAGS) bpReg.sv
	verilator $(VERILATOR_FLAGS) bpCorrelator.sv
	verilator $(VERILATOR_FLAGS) usbfsBpCorrelator.sv
	verilator $(VERILATOR_FLAGS) -I../../hdl/primitives/xilinx_7s pll48.sv
	verilator $(VERILATOR_FLAGS) -I../../hdl/primitives/xilinx_7s top.sv

IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I../../hdl
lint_iverilog:
	iverilog $(IVERILOG_FLAGS) -i correlator.sv
	iverilog $(IVERILOG_FLAGS) -i bpReg.sv
	iverilog $(IVERILOG_FLAGS) -i bpCorrelator.sv
	iverilog $(IVERILOG_FLAGS) -i usbfsBpCorrelator.sv
	iverilog $(IVERILOG_FLAGS) -i pll48.sv
	iverilog $(IVERILOG_FLAGS) -i top.sv

# pll48.sv emits warnings because the PLL primitive uses real parameters which
# yosys treats as strings.
lint_yosys:
	yosys -q -p 'read_verilog -sv -I../../hdl/ correlator.sv'
	yosys -q -p 'read_verilog -sv -I../../hdl/ bpReg.sv'
	yosys -q -p 'read_verilog -sv -I../../hdl/ bpCorrelator.sv'
	yosys -q -p 'read_verilog -sv -I../../hdl/ usbfsBpCorrelator.sv'
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
.PHONY: default synth signoff prog clean
.PHONY: lint lint_verilator lint_iverilog lint_yosys
