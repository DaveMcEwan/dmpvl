
# Dave McEwan 2020-10-01


PROJ := top
BUILD := ./build

SRC := \
	../../hdl/fpgaReset.sv \
	../../hdl/usbfsPktRx.sv \
	../../hdl/usbfsPktTx.sv \
	../../hdl/usbfsTxn.sv \
	../../hdl/usbfsEndpRx.sv \
	../../hdl/usbfsEndpTx.sv \
	../../hdl/usbfsEndpCtrlSerial.sv \
	../../hdl/usbfsSerial.sv \
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
	pll48.sv \
	correlator.sv \
	bpReg.sv \
	$(PROJ).sv

default: lint iverilog synth

synth: $(BUILD)/correlator.bit

# Use Verilator's LINT mode to ensure there's nothing too obviously wrong.
# This also ensures files are compatible with verilator.
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I../../hdl
lint:
	verilator $(VERILATOR_FLAGS) bpReg.sv
	verilator $(VERILATOR_FLAGS) correlator.sv
	verilator $(VERILATOR_FLAGS) -I../../hdl/primitives/xilinx_7s pll48.sv
	verilator $(VERILATOR_FLAGS) -I../../hdl/primitives/xilinx_7s top.sv

# Run through iverilog (Icarus) to ensure files are compatible.
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I../../hdl
iverilog:
	iverilog $(IVERILOG_FLAGS) -i bpReg.sv
	iverilog $(IVERILOG_FLAGS) -i correlator.sv
	iverilog $(IVERILOG_FLAGS) -i pll48.sv
	iverilog $(IVERILOG_FLAGS) -i top.sv

$(BUILD)/correlator.bit: $(SRC) vivado.tcl vc707.xdc
	vivado -mode batch -source vivado.tcl

# For this target to work ssh must be setup appropriately using ~/.ssh/config
# on the host.
# E.G. Something like this:
#  Host zc702
#  Hostname 192.168.0.10
#  User root
#  StrictHostKeyChecking no
#  UserKnownHostsFile /dev/null
#  LogLevel QUIET
prog: $(BUILD)/$(PROJ).vivado.bin
	scp $(BUILD)/$(PROJ).vivado.bin zc702:~/
	ssh zc702 -C "cat $(PROJ).vivado.bin > /dev/xdevcfg"

clean:
	rm -rf build
	rm -rf .cache
	rm -rf .Xil
	rm -rf usage_statistics*
	rm -rf vivado*.log
	rm -rf vivado*.jou

.SECONDARY:
.PHONY: default lint iverilog synth prog clean
