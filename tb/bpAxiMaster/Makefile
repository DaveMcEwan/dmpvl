
TB := bpAxiMaster_tb

V_SRC := \
	../../hdl/fifo.v \
	../../hdl/resetDetect.v \
	../../hdl/prngXoroshiro128p.v \
	../../hdl/axi4liteRandomSlave.v \
	../../hdl/bpAxiMaster.v \
	../../verif/generateClock.v \
	../../verif/bpPacketSender.v \
	driveBpPacket.v \
	checkBpToAxi.v \
	$(TB).v

# NOTE: Icarus only - no support for Verilator yet.
VCD_VERILATOR :=

LINT_SRC := ../../hdl/bpAxiMaster.v

include ../common.mk
