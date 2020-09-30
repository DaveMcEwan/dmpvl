
# As a basic sanity check `make` should complete with no warnings or errors.
all: lint iverilog yosys

# Use Verilator's LINT mode to ensure there's nothing too obviously wrong.
# This also ensures files are compatible with verilator.
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I../hdl
lint:
	verilator $(VERILATOR_FLAGS) generateClock.sv
	verilator $(VERILATOR_FLAGS) tristateBuffer.sv
	verilator $(VERILATOR_FLAGS) usbFullSpeedPacketSender.sv
	verilator $(VERILATOR_FLAGS) usbFullSpeedPacketReceiver.sv
	verilator $(VERILATOR_FLAGS) usbFullSpeedTransactor.sv
	verilator $(VERILATOR_FLAGS) usbFullSpeedEndpointSender.sv
	verilator $(VERILATOR_FLAGS) usbFullSpeedEndpointReceiver.sv
	verilator $(VERILATOR_FLAGS) usbFullSpeedControlSerial.sv
	verilator $(VERILATOR_FLAGS) usbFullSpeedSerial.sv

# None of these modules actually simulate anything useful on their own but try
# running them through iverilog (Icarus) to ensure files are compatible.
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I../hdl
iverilog:
	iverilog $(IVERILOG_FLAGS) generateClock.sv
	iverilog $(IVERILOG_FLAGS) tristateBuffer.sv
	iverilog $(IVERILOG_FLAGS) usbFullSpeedPacketSender.sv
	iverilog $(IVERILOG_FLAGS) usbFullSpeedPacketReceiver.sv
	iverilog $(IVERILOG_FLAGS) -i usbFullSpeedTransactor.sv
	iverilog $(IVERILOG_FLAGS) usbFullSpeedEndpointSender.sv
	iverilog $(IVERILOG_FLAGS) -i usbFullSpeedEndpointReceiver.sv
	iverilog $(IVERILOG_FLAGS) usbFullSpeedControlSerial.sv
	iverilog $(IVERILOG_FLAGS) -i usbFullSpeedSerial.sv

# None of these modules actually synthesize to anything useful on their own but
# try reading them with yosys, to ensure files are compatible.
# Only modules which are actually intended to be synthisizable.
yosys:
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedPacketSender.sv'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedPacketReceiver.sv'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedTransactor.sv'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedEndpointSender.sv'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedEndpointReceiver.sv'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedControlSerial.sv'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedSerial.sv'

.SECONDARY:
.PHONY: lint iverilog yosys
