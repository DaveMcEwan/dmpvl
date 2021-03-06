
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

# `make prog run` should work, but requires VC707 to be turned on while the
# synthesis step takes its time.
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

UST_CONN_SRC := $(BUILD)/$(DELIVERY)/ust_connection_utilities_release/ust_conn_usb
$(BUILD)/ust_conn_usb: $(UNPACKED)
	cd $(UST_CONN_SRC); make
	cp $(UST_CONN_SRC)/ust_conn_usb $@

# NOTE: All UltraSoC RTL files are Verilog2001 with .v extension, and any .sv
# files are only for verif so are excluded from this generated script.
# Desigs files from dmpvl are SystemVerilog2005 with .sv extension, so must be
# added separately in vivado.tcl like other project in dmpvl.
VERILATOR_LANG ?= --language 1800-2005
PREPROC_DEFINES += SYNTHESIS=1
PREPROC_DEFINES += ust_fpga_c=1
PREPROC_DEFINES += ust_vivado_c=1
PREPROC_DEFINES += ust_use_msg_slice_c=1
PREPROC_DIR := $(BUILD)/preproc
DELIVERY_EXCLUDE := (_bfm_|_dpi_|_sw_link_|_tb_)
DELIVERY_INCDIR := $(shell dirname $(UNPACKED))/inc
DELIVERY_SRCDIR := $(shell dirname $(UNPACKED))/src
DELIVERY_SRC = $(shell ls $(DELIVERY_SRCDIR)/*.v | grep -vE '$(DELIVERY_EXCLUDE)')
$(BUILD)/vivado-addFiles.tcl: $(UNPACKED)
	mkdir -p $(PREPROC_DIR)
	echo "add_files \\" > $@
	for f in $(DELIVERY_SRC); do \
		p=$(PREPROC_DIR)/`basename $$f`; \
		echo "  $$p \\" >> $@; \
		verilator -E -P -Mdir $(BUILD)/obj_dir $(VERILATOR_LANG) \
			-I$(DELIVERY_INCDIR) $(addprefix +define+,$(PREPROC_DEFINES)) \
			$$f > $$p; \
	done
	echo "" >> $@
preproc: $(BUILD)/vivado-addFiles.tcl
.PHONY: preproc

BITFILE ?= $(BUILD)/$(PRJ).bit
$(BITFILE): $(SRC_TOP) vivado-synth.tcl vc707.xdc
$(BITFILE): $(BUILD)/vivado-addFiles.tcl
$(BITFILE): $(BUILD)/ust_conn_usb
$(BITFILE):
	vivado -mode batch -source vivado-synth.tcl -tclargs --prj $(PRJ) --part $(PART) \
	--dirBuild $(BUILD) --deliveryIncdir $(DELIVERY_INCDIR) >> /dev/null
synth: $(BITFILE)
.PHONY: synth

# NOTE: Running with `python -m` means paths must be relative to py_link.
PYLINK_FLAGS += --verbose
PYLINK_FLAGS += --manual
PYLINK_FLAGS += --target=none
PYLINK_FLAGS += --communicator=usb
PYLINK_FLAGS += --communicator-type=usb
PYLINK_FLAGS += --launch-cmd="../../ust_conn_usb"
PYLINK_FLAGS += --messages-xml="../messages.xml"
PYLINK_FLAGS += --registry-xml="../registry.xml"
ifneq ($(TEST),)
PYLINK_FLAGS += --system-xml="../system-discovered.xml"
endif
# NOTE: Default value of TEST must be defined after the above ifneq.
# General discovery test produces what is contained in system-discovered.xml, so
# XML must not be provided in that case.
TEST ?= py_link/tests/general-discovery.py
TEST_PARAMS += timeout-seconds=2
run: $(BUILD)/ust_conn_usb
	cd $(BUILD)/$(DELIVERY); python3 -m py_link.run_test \
		$(PYLINK_FLAGS) \
		$(TEST) \
		$(TEST_PARAMS) > $(basename $(notdir $(TEST))).log
.PHONY: run

prog:
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

