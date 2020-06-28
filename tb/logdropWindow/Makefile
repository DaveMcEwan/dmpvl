
TB := logdropWindow_tb

V_SRC := \
	../../hdl/fxcs.v \
	../../hdl/onehotIdx.v \
	../../hdl/mssbIdx.v \
	../../hdl/logdropWindow.v \
	$(TB).v

# NOTE: Verilator only - no support for Icarus yet.
VCD_IVERILOG :=

include ../common.mk


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
		w_rand.v
	make -j -C $(BUILD) -f Vw_rand.mk Vw_rand
	time $(BUILD)/Vw_rand > $(BUILD)/w_rand.log
	@! grep -q ERROR ./build/Vw_rand.log
	plotDistBytes $(BUILD)/w_rand.i_x.bin -o w_rand.i_x
	plotDistBytes $(BUILD)/w_rand.o_y.bin -o w_rand.o_y
