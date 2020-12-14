
# Dave McEwan 2020-01-21

SRC := \
	../../hdl/fifoW1R1.sv \
	../../hdl/fpgaReset.sv \
	../../verif/usbFullSpeedPacketReceiver.sv \
	../../verif/usbFullSpeedPacketSender.sv \
	../../verif/usbFullSpeedTransactor.sv \
	../../verif/usbFullSpeedEndpointReceiver.sv \
	../../verif/usbFullSpeedEndpointSender.sv \
	../../verif/usbFullSpeedControlSerial.sv \
	../../verif/usbFullSpeedSerial.sv \
	./build/pll48.sv \
	top.sv

include ../common_ice40.mk

MULTIPNR_MK := ../multipnr_ice40.mk
MULTIPNR_ARACHNE := 1
include $(MULTIPNR_MK)
