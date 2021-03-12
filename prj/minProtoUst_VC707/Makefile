
DELIVERY_ENCRYPTED ?= protofiles.enc
DELIVERY := $(basename $(DELIVERY_ENCRYPTED))

# Dave McEwan 2021-03-12

PRJ ?= minProtoUst
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
PART := xc7vx485tffg1761-2

SRC_TOP := \
	../../hdl/fpgaReset.sv \
	../../hdl/fifoW1R1.sv \
	../../hdl/fxcs.sv \
	../../hdl/logdropWindow.sv \
	../../hdl/mssbIdx.sv \
	../../hdl/onehotIdx.sv \
	../../hdl/prngXoshiro128p.sv \
	../../hdl/strobe.sv \
	../../hdl/syncBit.sv \
	../../hdl/pwm.sv \
	../../hdl/dividerFsm.sv \
	../../hdl/corrCountRect.sv \
	../../hdl/corrCountLogdrop.sv \
	../../hdl/xbar.sv \
	correlator.sv \
	pll.sv \
	top.sv

default: synth

# Delivery is a gzipped tarball encrypted with:
#   openssl enc -e -md sha256 -bf-cbc -a -salt -in delivery.tar.gz
TARBALL := $(BUILD)/$(DELIVERY).tar.gz
$(TARBALL): $(DELIVERY_ENCRYPTED)
	mkdir -p $(BUILD)
	openssl enc -d -md sha256 -bf-cbc -a -in $(DELIVERY_ENCRYPTED) > $@
decrypt: $(TARBALL)
.PHONY: decrypt

# Uncompress, unpack, and create a magic file for Make's dependency tracking.
UNPACKED := $(BUILD)/$(DELIVERY)/unpacked
$(UNPACKED): $(TARBALL)
	cd $(shell dirname $(TARBALL)); tar -xzf $(shell basename $(TARBALL))
	touch $(UNPACKED)
unpack: $(UNPACKED)
.PHONY: unpack

# NOTE: All UltraSoC RTL files are Verilog2001 with .v extension, and any .sv
# files are only for verif so are excluded from this generated script.
# Desigs files from dmpvl are SystemVerilog2005 with .sv extension, so must be
# added separately in vivado.tcl like other project in dmpvl.
DELIVERY_EXCLUDE := (_bfm_|_dpi_|_sw_link_|_tb_)
DELIVERY_INCDIR := $(shell dirname $(UNPACKED))/inc
DELIVERY_SRCDIR := $(shell dirname $(UNPACKED))/src
DELIVERY_SRC = $(shell ls $(DELIVERY_SRCDIR)/*.v | grep -vE '$(DELIVERY_EXCLUDE)')
$(BUILD)/vivado-addFiles.tcl: $(UNPACKED)
	echo "add_files \\" > $@
	for f in $(DELIVERY_SRC); do echo "  $$f \\" >> $@; done
	echo "" >> $@

BITFILE ?= $(BUILD)/$(PRJ).bit
$(BITFILE): $(BUILD)/vivado-addFiles.tcl $(SRC_TOP) vivado.tcl vc707.xdc
	vivado -mode batch -source vivado.tcl -tclargs --prj $(PRJ) --part $(PART) \
	--dirBuild $(BUILD) --deliveryIncdir $(DELIVERY_INCDIR)
synth: $(BITFILE)
.PHONY: synth

prog: $(BITFILE)
	vivado -mode batch -source ../../tcl/vivado-program.tcl \
		-tclargs --part $(PART) --bitstream $(BITFILE)
.PHONY: prog

clean:
	rm -rf build
	rm -rf .cache
	rm -rf .Xil
	rm -rf usage_statistics*
	rm -rf vivado*.log
	rm -rf vivado*.jou
	rm -rf webtalk*.log
	rm -rf webtalk*.jou
.PHONY: clean

