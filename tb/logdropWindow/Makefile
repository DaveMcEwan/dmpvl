
SRC_SINGLEHIER += ../../hdl/fxcs.sv
SRC_SINGLEHIER += ../../hdl/onehotIdx.sv

SRC_MULTIHIER += ../../hdl/mssbIdx.sv
SRC_MULTIHIER += ../../hdl/logdropWindow.sv
SRC_MULTIHIER += logdropWindow_tb.sv

IVERILOG_SRC_EXCLUDE += logdropWindow_tb.sv
YOSYS_SRC_EXCLUDE += logdropWindow_tb.sv

default: lint_foss
default: verilator_vcd

MK_TB = ../../mk/tb.mk
include $(MK_TB)

# NOTE: plotDistBytes is bundled with dmppl.
w_rand:
	mkdir -p $(BUILD)
	verilator --cc \
		--trace \
		--trace-depth 3 \
		--exe \
		-I../../hdl/ \
		--Mdir $(BUILD) \
		--top-module w_rand \
		w_rand.cc \
		w_rand.sv
	make -j -C $(BUILD) -f Vw_rand.mk Vw_rand
	time $(BUILD)/Vw_rand > $(BUILD)/w_rand.log
	@! grep -q ERROR ./build/Vw_rand.log
	plotDistBytes $(BUILD)/w_rand.i_x.bin -o w_rand.i_x
	plotDistBytes $(BUILD)/w_rand.o_y.bin -o w_rand.o_y
