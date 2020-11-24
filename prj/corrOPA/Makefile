
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


PART := xc7vx485tffg1761-2
BITFILE ?= openpiton/build/vc707/system/vc707_system/vc707_system.runs/impl_1/system.bit

$(BITFILE):
	cd openpiton; protosyn --board=vc707 --core=ariane --uart-dmw=ddr --x_tiles=3

rmbit:
	rm -f $(BITFILE)

prog: $(BITFILE)
	vivado -mode batch -source ../../tcl/vivado-program.tcl \
		-tclargs --part $(PART) --bitstream $(BITFILE)


clean:
	rm -rf openpiton/build/vc707
	cd openpiton: git checkout piton/design/chipset/xilinx/vc707/ip_cores/clk_mmcm/clk_mmcm.xci
	cd openpiton: git checkout piton/design/chipset/rtl/chipset.v
	cd openpiton: git checkout piton/design/xilinx/vc707/constraints.xdc
	cd openpiton: git checkout piton/tools/src/proto/common/rtl_setup.tcl
	cd openpiton: git checkout piton/design/rtl/system.v

.PHONY: patchset rmbit prog clean
