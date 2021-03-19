
# As a basic sanity check `make` should complete with no warnings or errors.
default: lint_foss
all: preproc lint_foss lint_paid

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

INCDIRS = .

MK_LINT := ../mk/lint.mk
include $(MK_LINT)

MK_PREPROC := ../mk/preproc.mk
include $(MK_PREPROC)

