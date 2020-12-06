
# As a basic sanity check `make` should complete with no warnings or errors.
default: lint iverilog yosys
all: lint iverilog yosys vivado

# Use Verilator's LINT mode to ensure there's nothing too obviously wrong.
# This also ensures files are compatible with verilator.
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG)
lint:
	verilator $(VERILATOR_FLAGS) axi4liteMonitor.sv
	verilator $(VERILATOR_FLAGS) axi4liteRandomMaster.sv
	verilator $(VERILATOR_FLAGS) axi4liteRandomSlave.sv
	verilator $(VERILATOR_FLAGS) binToGray.sv
	verilator $(VERILATOR_FLAGS) bpRegMem.sv
	verilator $(VERILATOR_FLAGS) cdcData.sv
	verilator $(VERILATOR_FLAGS) cdcFifo.sv
	verilator $(VERILATOR_FLAGS) corrCountLogdrop.sv
	verilator $(VERILATOR_FLAGS) corrCountRect.sv
	verilator $(VERILATOR_FLAGS) dividerFsm.sv
	verilator $(VERILATOR_FLAGS) edgeDetect.sv
	verilator $(VERILATOR_FLAGS) fifoW1R1.sv
	verilator $(VERILATOR_FLAGS) fpgaReset.sv
	verilator $(VERILATOR_FLAGS) fxcs.sv
	verilator $(VERILATOR_FLAGS) grayCounter.sv
	verilator $(VERILATOR_FLAGS) grayToBin.sv
	verilator $(VERILATOR_FLAGS) logdropWindow.sv
	verilator $(VERILATOR_FLAGS) mssbIdx.sv
	verilator $(VERILATOR_FLAGS) onehotIdx.sv
	verilator $(VERILATOR_FLAGS) popcnt6.sv
	verilator $(VERILATOR_FLAGS) prngXoroshiro128p.sv
	verilator $(VERILATOR_FLAGS) prngXoroshiro64s.sv
	verilator $(VERILATOR_FLAGS) prngXoshiro128pp.sv
	verilator $(VERILATOR_FLAGS) prngXoshiro128p.sv
	verilator $(VERILATOR_FLAGS) prngXoshiro256p.sv
	verilator $(VERILATOR_FLAGS) pwm.sv
	verilator $(VERILATOR_FLAGS) resetDetect.sv
	verilator $(VERILATOR_FLAGS) strobe.sv
	verilator $(VERILATOR_FLAGS) syncBit.sv
	verilator $(VERILATOR_FLAGS) usbfsEndpCtrlSerial.sv
	verilator $(VERILATOR_FLAGS) usbfsEndpRx.sv
	verilator $(VERILATOR_FLAGS) usbfsEndpTx.sv
	verilator $(VERILATOR_FLAGS) usbfsPktRx.sv
	verilator $(VERILATOR_FLAGS) usbfsPktTx.sv
	verilator $(VERILATOR_FLAGS) usbfsSerial.sv
	verilator $(VERILATOR_FLAGS) usbfsTxn.sv
	verilator $(VERILATOR_FLAGS) xbar.sv

# None of these modules actually simulate anything useful on their own but try
# running them through iverilog (Icarus) to ensure files are compatible.
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null
iverilog:
	iverilog $(IVERILOG_FLAGS) axi4liteMonitor.sv
	iverilog $(IVERILOG_FLAGS) -i axi4liteRandomMaster.sv
	iverilog $(IVERILOG_FLAGS) -i axi4liteRandomSlave.sv
	iverilog $(IVERILOG_FLAGS) binToGray.sv
	iverilog $(IVERILOG_FLAGS) bpRegMem.sv
	iverilog $(IVERILOG_FLAGS) -i cdcData.sv
	iverilog $(IVERILOG_FLAGS) -i cdcFifo.sv
	iverilog $(IVERILOG_FLAGS) -i corrCountLogdrop.sv
	iverilog $(IVERILOG_FLAGS) corrCountRect.sv
	iverilog $(IVERILOG_FLAGS) dividerFsm.sv
	iverilog $(IVERILOG_FLAGS) edgeDetect.sv
	iverilog $(IVERILOG_FLAGS) fifoW1R1.sv
	iverilog $(IVERILOG_FLAGS) fpgaReset.sv
	iverilog $(IVERILOG_FLAGS) fxcs.sv
	iverilog $(IVERILOG_FLAGS) grayCounter.sv
	iverilog $(IVERILOG_FLAGS) grayToBin.sv
	iverilog $(IVERILOG_FLAGS) -i logdropWindow.sv
	iverilog $(IVERILOG_FLAGS) -i mssbIdx.sv
	iverilog $(IVERILOG_FLAGS) onehotIdx.sv
	iverilog $(IVERILOG_FLAGS) popcnt6.sv
	iverilog $(IVERILOG_FLAGS) prngXoroshiro128p.sv
	iverilog $(IVERILOG_FLAGS) prngXoroshiro64s.sv
	iverilog $(IVERILOG_FLAGS) prngXoshiro128pp.sv
	iverilog $(IVERILOG_FLAGS) prngXoshiro128p.sv
	iverilog $(IVERILOG_FLAGS) prngXoshiro256p.sv
	iverilog $(IVERILOG_FLAGS) pwm.sv
	iverilog $(IVERILOG_FLAGS) resetDetect.sv
	iverilog $(IVERILOG_FLAGS) -i strobe.sv
	iverilog $(IVERILOG_FLAGS) syncBit.sv
	iverilog $(IVERILOG_FLAGS) usbfsEndpCtrlSerial.sv
	iverilog $(IVERILOG_FLAGS) -i usbfsEndpRx.sv
	iverilog $(IVERILOG_FLAGS) -i usbfsEndpTx.sv
	iverilog $(IVERILOG_FLAGS) usbfsPktRx.sv
	iverilog $(IVERILOG_FLAGS) usbfsPktTx.sv
	iverilog $(IVERILOG_FLAGS) -i usbfsSerial.sv
	iverilog $(IVERILOG_FLAGS) -i usbfsTxn.sv
	iverilog $(IVERILOG_FLAGS) -i xbar.sv

# None of these modules actually synthesize to anything useful on their own but
# try reading them with yosys, to ensure files are compatible.
yosys:
	yosys -q -p 'read_verilog -sv axi4liteMonitor.sv'
	yosys -q -p 'read_verilog -sv axi4liteRandomMaster.sv'
	yosys -q -p 'read_verilog -sv axi4liteRandomSlave.sv'
	yosys -q -p 'read_verilog -sv binToGray.sv'
	yosys -q -p 'read_verilog -sv bpRegMem.sv'
	yosys -q -p 'read_verilog -sv cdcData.sv'
	yosys -q -p 'read_verilog -sv cdcFifo.sv'
	yosys -q -p 'read_verilog -sv corrCountLogdrop.sv'
	yosys -q -p 'read_verilog -sv corrCountRect.sv'
	yosys -q -p 'read_verilog -sv dividerFsm.sv'
	yosys -q -p 'read_verilog -sv edgeDetect.sv'
	yosys -q -p 'read_verilog -sv fifoW1R1.sv'
	yosys -q -p 'read_verilog -sv fpgaReset.sv'
	yosys -q -p 'read_verilog -sv fxcs.sv'
	yosys -q -p 'read_verilog -sv grayCounter.sv'
	yosys -q -p 'read_verilog -sv grayToBin.sv'
	yosys -q -p 'read_verilog -sv logdropWindow.sv'
	yosys -q -p 'read_verilog -sv mssbIdx.sv'
	yosys -q -p 'read_verilog -sv onehotIdx.sv'
	yosys -q -p 'read_verilog -sv popcnt6.sv'
	yosys -q -p 'read_verilog -sv prngXoroshiro128p.sv'
	yosys -q -p 'read_verilog -sv prngXoroshiro64s.sv'
	yosys -q -p 'read_verilog -sv prngXoshiro128pp.sv'
	yosys -q -p 'read_verilog -sv prngXoshiro128p.sv'
	yosys -q -p 'read_verilog -sv prngXoshiro256p.sv'
	yosys -q -p 'read_verilog -sv pwm.sv'
	yosys -q -p 'read_verilog -sv resetDetect.sv'
	yosys -q -p 'read_verilog -sv strobe.sv'
	yosys -q -p 'read_verilog -sv syncBit.sv'
	yosys -q -p 'read_verilog -sv usbfsEndpCtrlSerial.sv'
	yosys -q -p 'read_verilog -sv usbfsEndpRx.sv'
	yosys -q -p 'read_verilog -sv usbfsEndpTx.sv'
	yosys -q -p 'read_verilog -sv usbfsPktRx.sv'
	yosys -q -p 'read_verilog -sv usbfsPktTx.sv'
	yosys -q -p 'read_verilog -sv usbfsSerial.sv'
	yosys -q -p 'read_verilog -sv usbfsTxn.sv'
	yosys -q -p 'read_verilog -sv xbar.sv'

# Tested with Vivado 2018.2
define VIVADO_TCL =
create_project -in_memory projectDummy
create_fileset -blockset filesetDummy
add_files \\
	axi4liteMonitor.sv \\
	axi4liteRandomMaster.sv \\
	axi4liteRandomSlave.sv \\
	binToGray.sv \\
	bpRegMem.sv \\
	cdcData.sv \\
	cdcFifo.sv \\
	corrCountLogdrop.sv \\
	corrCountRect.sv \\
	dividerFsm.sv \\
	edgeDetect.sv \\
	fifoW1R1.sv \\
	fpgaReset.sv \\
	fxcs.sv \\
	grayCounter.sv \\
	grayToBin.sv \\
	logdropWindow.sv \\
	mssbIdx.sv \\
	onehotIdx.sv \\
	popcnt6.sv \\
	prngXoroshiro128p.sv \\
	prngXoroshiro64s.sv \\
	prngXoshiro128pp.sv \\
	prngXoshiro128p.sv \\
	prngXoshiro256p.sv \\
	pwm.sv \\
	resetDetect.sv \\
	strobe.sv \\
	syncBit.sv \\
	usbfsEndpCtrlSerial.sv \\
	usbfsEndpRx.sv \\
	usbfsEndpTx.sv \\
	usbfsPktRx.sv \\
	usbfsPktTx.sv \\
	usbfsSerial.sv \\
	usbfsTxn.sv \\
	xbar.sv \\
	-fileset filesetDummy
check_syntax -fileset filesetDummy
endef
export VIVADO_TCL
vivado:
	rm -f vivado_*.backup.jou
	rm -f vivado_*.backup.log
	rm -f webtalk*
	@echo "$$VIVADO_TCL" > vivado.tcl
	vivado -mode batch -source vivado.tcl > /dev/null
	@! grep -q ERROR vivado.log
	@! grep -q WARNING vivado.log

.SECONDARY:
.PHONY: lint iverilog yosys vivado
