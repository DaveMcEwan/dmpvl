
# As a basic sanity check `make` should complete with no warnings or errors.
all: lint iverilog yosys

# Use Verilator's LINT mode to ensure there's nothing too obviously wrong.
# This also ensures files are compatible with verilator.
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG)
lint:
	verilator $(VERILATOR_FLAGS) bpRegMem.v
	verilator $(VERILATOR_FLAGS) logdropWindow.v
	verilator $(VERILATOR_FLAGS) dividerFsm.v
	verilator $(VERILATOR_FLAGS) edgeDetect.v
	verilator $(VERILATOR_FLAGS) resetDetect.v
	verilator $(VERILATOR_FLAGS) fifo.v
	verilator $(VERILATOR_FLAGS) popcnt6.v
	verilator $(VERILATOR_FLAGS) onehotIdx.v
	verilator $(VERILATOR_FLAGS) fxcs.v
	verilator $(VERILATOR_FLAGS) mssbIdx.v
	verilator $(VERILATOR_FLAGS) strobe.v
	verilator $(VERILATOR_FLAGS) pwm.v
	verilator $(VERILATOR_FLAGS) prngXoroshiro128p.v
	verilator $(VERILATOR_FLAGS) prngXoshiro128pp.v
	verilator $(VERILATOR_FLAGS) prngXoshiro128p.v
	verilator $(VERILATOR_FLAGS) prngXoshiro256p.v
	verilator $(VERILATOR_FLAGS) prngXoroshiro64s.v
	verilator $(VERILATOR_FLAGS) axi4liteMonitor.v
	verilator $(VERILATOR_FLAGS) axi4liteRandomSlave.v
	verilator $(VERILATOR_FLAGS) axi4liteRandomMaster.v
	verilator $(VERILATOR_FLAGS) usbfsPktRx.v
	verilator $(VERILATOR_FLAGS) usbfsPktTx.v
	verilator $(VERILATOR_FLAGS) usbfsTxn.v
	verilator $(VERILATOR_FLAGS) usbfsEndpRx.v
	verilator $(VERILATOR_FLAGS) usbfsEndpTx.v
	verilator $(VERILATOR_FLAGS) usbfsEndpCtrlSerial.v
	verilator $(VERILATOR_FLAGS) usbfsSerial.v

# None of these modules actually simulate anything useful on their own but try
# running them through iverilog (Icarus) to ensure files are compatible.
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null
iverilog:
	iverilog $(IVERILOG_FLAGS) bpRegMem.v
	iverilog $(IVERILOG_FLAGS) -i logdropWindow.v
	iverilog $(IVERILOG_FLAGS) dividerFsm.v
	iverilog $(IVERILOG_FLAGS) edgeDetect.v
	iverilog $(IVERILOG_FLAGS) resetDetect.v
	iverilog $(IVERILOG_FLAGS) fifo.v
	iverilog $(IVERILOG_FLAGS) popcnt6.v
	iverilog $(IVERILOG_FLAGS) onehotIdx.v
	iverilog $(IVERILOG_FLAGS) fxcs.v
	iverilog $(IVERILOG_FLAGS) -i mssbIdx.v
	iverilog $(IVERILOG_FLAGS) -i strobe.v
	iverilog $(IVERILOG_FLAGS) pwm.v
	iverilog $(IVERILOG_FLAGS) prngXoroshiro128p.v
	iverilog $(IVERILOG_FLAGS) prngXoshiro128pp.v
	iverilog $(IVERILOG_FLAGS) prngXoshiro128p.v
	iverilog $(IVERILOG_FLAGS) prngXoshiro256p.v
	iverilog $(IVERILOG_FLAGS) prngXoroshiro64s.v
	iverilog $(IVERILOG_FLAGS) axi4liteMonitor.v
	iverilog $(IVERILOG_FLAGS) -i axi4liteRandomSlave.v
	iverilog $(IVERILOG_FLAGS) -i axi4liteRandomMaster.v
	iverilog $(IVERILOG_FLAGS) usbfsPktRx.v
	iverilog $(IVERILOG_FLAGS) usbfsPktTx.v
	iverilog $(IVERILOG_FLAGS) -i usbfsTxn.v
	iverilog $(IVERILOG_FLAGS) -i usbfsEndpRx.v
	iverilog $(IVERILOG_FLAGS) -i usbfsEndpTx.v
	iverilog $(IVERILOG_FLAGS) usbfsEndpCtrlSerial.v
	iverilog $(IVERILOG_FLAGS) -i usbfsSerial.v

# None of these modules actually synthesize to anything useful on their own but
# try reading them with yosys, to ensure files are compatible.
yosys:
	yosys -q -p 'read_verilog -sv bpRegMem.v'
	yosys -q -p 'read_verilog -sv logdropWindow.v'
	yosys -q -p 'read_verilog -sv dividerFsm.v'
	yosys -q -p 'read_verilog -sv edgeDetect.v'
	yosys -q -p 'read_verilog -sv resetDetect.v'
	yosys -q -p 'read_verilog -sv fifo.v'
	yosys -q -p 'read_verilog -sv popcnt6.v'
	yosys -q -p 'read_verilog -sv onehotIdx.v'
	yosys -q -p 'read_verilog -sv fxcs.v'
	yosys -q -p 'read_verilog -sv mssbIdx.v'
	yosys -q -p 'read_verilog -sv strobe.v'
	yosys -q -p 'read_verilog -sv pwm.v'
	yosys -q -p 'read_verilog -sv prngXoroshiro128p.v'
	yosys -q -p 'read_verilog -sv prngXoshiro128pp.v'
	yosys -q -p 'read_verilog -sv prngXoshiro128p.v'
	yosys -q -p 'read_verilog -sv prngXoshiro256p.v'
	yosys -q -p 'read_verilog -sv prngXoroshiro64s.v'
	yosys -q -p 'read_verilog -sv axi4liteMonitor.v'
	yosys -q -p 'read_verilog -sv axi4liteRandomSlave.v'
	yosys -q -p 'read_verilog -sv axi4liteRandomMaster.v'
	yosys -q -p 'read_verilog -sv usbfsPktRx.v'
	yosys -q -p 'read_verilog -sv usbfsPktTx.v'
	yosys -q -p 'read_verilog -sv usbfsTxn.v'
	yosys -q -p 'read_verilog -sv usbfsEndpRx.v'
	yosys -q -p 'read_verilog -sv usbfsEndpTx.v'
	yosys -q -p 'read_verilog -sv usbfsEndpCtrlSerial.v'
	yosys -q -p 'read_verilog -sv usbfsSerial.v'

.SECONDARY:
.PHONY: lint iverilog yosys
