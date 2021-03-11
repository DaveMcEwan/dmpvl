
DELIVERY_ENCRYPTED ?= protofiles.enc
DELIVERY := $(basename $(DELIVERY_ENCRYPTED))

PRJ ?= minProtoUst

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



# Delivery is a gzipped tarball encrypted with:
#   openssl enc -bf-cbc -a -salt -in delivery.tar.gz
TARBALL ?= $(DELIVERY).tar.gz
$(TARBALL): $(DELIVERY_ENCRYPTED)
	openssl enc -d -bf-cbc -a -in $(DELIVERY_ENCRYPTED) > $@
decrypt: $(TARBALL)
.PHONY: decrypt

# Uncompress, unpack, and create a magic file for Make's dependency tracking.
UNPACKED := $(DELIVERY)/unpacked
$(UNPACKED): $(TARBALL)
	tar -xzvf $(TARBALL)
	touch $(UNPACKED)
unpack: $(UNPACKED)
.PHONY: unpack

DELIVERY_INC = $(shell ls $(DELIVERY)/inc/*.vh | grep -vE '(_dpi_|_tb_)')
DELIVERY_SRC = $(shell ls $(DELIVERY)/src/*.v | grep -vE '(_bfm_|_tb_)')
vivado-addFiles.tcl: $(UNPACKED)
	rm -f $@
	for f in $(DELIVERY_INC); do echo "add_files $$f" >> $@; done
	for f in $(DELIVERY_SRC); do echo "add_files $$f" >> $@; done

BITFILE ?= $(BUILD)/$(PRJ).bit
$(BITFILE): vivado-addFiles.tcl $(SRC_TOP) vivado.tcl vc707.xdc
	vivado -mode batch -source vivado.tcl \
		-tclargs --prj $(PRJ) --part $(PART) --dirBuild $(BUILD) \
			--synth_yosys $(SYNTH_YOSYS)
synth: $(BITFILE)
.PHONY: synth

prog: $(BITFILE)
	vivado -mode batch -source ../../tcl/vivado-program.tcl \
		-tclargs --part $(PART) --bitstream $(BITFILE)
.PHONY: prog

