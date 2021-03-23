# source /space/xilinx/Vivado/2018.2/settings64.sh
# pushd openpiton; source piton/ariane_setup.sh; popd
# make clean && make apply && make prog

apply:
	cd openpiton; git apply ../*.patch

PATCHSET =
PATCHSET += clk_mmcm.xci.patch
PATCHSET += chip.v.pyv.patch
PATCHSET += chipset.v.patch
PATCHSET += constraints.xdc.patch
PATCHSET += rtl_setup.tcl.patch
PATCHSET += system.v.patch

patchset: $(PATCHSET)

clk_mmcm.xci.patch:
	cd openpiton; git diff piton/design/chipset/xilinx/vc707/ip_cores/clk_mmcm/clk_mmcm.xci > ../$@
# NOTE: Rarely update clk_mmcm.xci.patch!

chip.v.pyv.patch:
	cd openpiton; git diff piton/design/chip/rtl/chip.v.pyv > ../$@
.PHONY: chip.v.pyv.patch

chipset.v.patch:
	cd openpiton; git diff piton/design/chipset/rtl/chipset.v > ../$@
.PHONY: chipset.v.patch

constraints.xdc.patch:
	cd openpiton; git diff piton/design/xilinx/vc707/constraints.xdc > ../$@
.PHONY: constraints.xdc.patch

rtl_setup.tcl.patch:
	cd openpiton; git diff piton/tools/src/proto/common/rtl_setup.tcl > ../$@
.PHONY: rtl_setup.tcl.patch

system.v.patch:
	cd openpiton; git diff piton/design/rtl/system.v > ../$@
.PHONY: system.v.patch

BUILD ?= ./build

PART := xc7vx485tffg1761-2
BITFILE ?= openpiton/build/vc707/system/vc707_system/vc707_system.runs/impl_1/system.bit

DELIVERY_ENCRYPTED ?= protofiles.enc
DELIVERY := $(basename $(DELIVERY_ENCRYPTED))

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
DELIVERY_EXCLUDE := (_bfm_|_dpi_|_sw_link_|_tb_)
DELIVERY_INCDIR := $(shell dirname $(UNPACKED))/inc
#DELIVERY_INC = $(shell ls $(DELIVERY_INCDIR)/*.vh | grep -vE '$(DELIVERY_EXCLUDE)')
#$(BUILD)/protofiles_inc.tcl: $(UNPACKED)
#	echo "set PROTOFILES_INC [list \\" > $@
#	for f in $(DELIVERY_INC); do echo "  \"\$${DV_ROOT}/../../$$f\" \\" >> $@; done
#	echo "]" >> $@
VERILATOR_LANG ?= --language 1800-2005
PREPROC_DEFINES += SYNTHESIS=1
PREPROC_DEFINES += ust_fpga_c=1
PREPROC_DEFINES += ust_vivado_c=1
PREPROC_DEFINES += ust_use_msg_slice_c=1
DELIVERY_SRCDIR := $(shell dirname $(UNPACKED))/src
DELIVERY_SRC = $(shell ls $(DELIVERY_SRCDIR)/*.v | grep -vE '$(DELIVERY_EXCLUDE)')
PREPROC_DIR := $(BUILD)/preproc
$(BUILD)/protofiles_src.tcl: $(UNPACKED)
	mkdir -p $(PREPROC_DIR)
	echo "set PROTOFILES_SRC [list \\" > $@
	for f in $(DELIVERY_SRC); do \
		p=$(PREPROC_DIR)/`basename $$f`; \
		echo "  \"\$${DV_ROOT}/../../$$p\" \\" >> $@; \
		verilator -E -P -Mdir $(BUILD)/obj_dir $(VERILATOR_LANG) \
			-I$(DELIVERY_INCDIR) $(addprefix +define+,$(PREPROC_DEFINES)) \
			$$f > $$p; \
	done
	echo "]" >> $@
preproc: $(BUILD)/protofiles_src.tcl
.PHONY: preproc


$(BITFILE): $(BUILD)/ust_conn_usb
#$(BITFILE): $(BUILD)/protofiles_inc.tcl
$(BITFILE): $(BUILD)/protofiles_src.tcl
$(BITFILE):
	cd openpiton; protosyn --board=vc707 --core=ariane --uart-dmw=ddr --x_tiles=3
synth: $(BITFILE)
.PHONY: synth

rmbit:
	rm -f $(BITFILE)

prog:
	vivado -mode batch -source ../../tcl/vivado-program.tcl \
		-tclargs --part $(PART) --bitstream $(BITFILE)

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


clean:
	rm -rf $(PREPROC_DIR) $(BUILD)/protofiles_src.tcl
	rm -rf openpiton/build/vc707
	cd openpiton; git checkout piton/design/chipset/xilinx/vc707/ip_cores/clk_mmcm/clk_mmcm.xci
	cd openpiton; git checkout piton/design/chip/rtl/chip.v.pyv
	cd openpiton; git checkout piton/design/chipset/rtl/chipset.v
	cd openpiton; git checkout piton/design/xilinx/vc707/constraints.xdc
	cd openpiton; git checkout piton/tools/src/proto/common/rtl_setup.tcl
	cd openpiton; git checkout piton/design/rtl/system.v

.PHONY: patchset rmbit prog clean

# Unpack protofiles from UltraSoC delivery
.PHONY: protofiles
protofiles:
	tar -xzvf protofiles.tar.gz
