
# As a basic sanity check `make` should complete with no warnings or errors.
all: lint iverilog yosys

# Use Verilator's LINT mode to ensure there's nothing too obviously wrong.
# This also ensures files are compatible with verilator.
VERILATOR_LANG ?= --language 1800-2005
VERILATOR_FLAGS := --lint-only $(VERILATOR_LANG) -I../hdl
lint:
	verilator $(VERILATOR_FLAGS) generateClock.v
	verilator $(VERILATOR_FLAGS) tristateBuffer.v
	verilator $(VERILATOR_FLAGS) usbFullSpeedPacketSender.v
	verilator $(VERILATOR_FLAGS) usbFullSpeedPacketReceiver.v
	verilator $(VERILATOR_FLAGS) usbFullSpeedTransactor.v
	verilator $(VERILATOR_FLAGS) usbFullSpeedEndpointSender.v
	verilator $(VERILATOR_FLAGS) usbFullSpeedEndpointReceiver.v
	verilator $(VERILATOR_FLAGS) usbFullSpeedControlSerial.v
	verilator $(VERILATOR_FLAGS) usbFullSpeedSerial.v

# None of these modules actually simulate anything useful on their own but try
# running them through iverilog (Icarus) to ensure files are compatible.
IVERILOG_LANG ?= -g2005-sv
IVERILOG_FLAGS := $(IVERILOG_LANG) -o /dev/null -I../hdl
iverilog:
	iverilog $(IVERILOG_FLAGS) generateClock.v
	iverilog $(IVERILOG_FLAGS) tristateBuffer.v
	iverilog $(IVERILOG_FLAGS) usbFullSpeedPacketSender.v
	iverilog $(IVERILOG_FLAGS) usbFullSpeedPacketReceiver.v
	iverilog $(IVERILOG_FLAGS) -i usbFullSpeedTransactor.v
	iverilog $(IVERILOG_FLAGS) usbFullSpeedEndpointSender.v
	iverilog $(IVERILOG_FLAGS) -i usbFullSpeedEndpointReceiver.v
	iverilog $(IVERILOG_FLAGS) usbFullSpeedControlSerial.v
	iverilog $(IVERILOG_FLAGS) -i usbFullSpeedSerial.v

# None of these modules actually synthesize to anything useful on their own but
# try reading them with yosys, to ensure files are compatible.
# Only modules which are actually intended to be synthisizable.
yosys:
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedPacketSender.v'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedPacketReceiver.v'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedTransactor.v'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedEndpointSender.v'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedEndpointReceiver.v'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedControlSerial.v'
	yosys -q -p 'read_verilog -sv -I../hdl usbFullSpeedSerial.v'

.SECONDARY:
.PHONY: lint iverilog yosys
