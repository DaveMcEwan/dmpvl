
# Default recipe here should try to build everything by running the default
# recipe in each relevant subdirectory.
# NOTE: Long running experiments like multipnr should not be run.
CSET := '\e[7m\e[32m'
CUNSET := '\e[27m\e[39m'
default: check_hdl check_verif verilator_tbs iverilog_tbs projects
	@echo topLevelMakefile UNBROKEN
	git diff --exit-code
	@echo topLevelMakefile NOTHING UNADDED
	git diff --exit-code --cached
	@echo topLevelMakefile NOTHING UNCOMMITED
	@echo -e topLevelMakefile $(CSET)PASS$(CUNSET) - Branch may be pushed.

check_hdl:
	make -C hdl

check_verif:
	make -C verif

# {{{ verilator

verilator_tbs: verilator_onehotIdx_tb
verilator_tbs: verilator_popcnt6_tb
verilator_tbs: verilator_fifo_tb
verilator_tbs: verilator_fxcs_tb

verilator_onehotIdx_tb:
	make -C tb/onehotIdx build/onehotIdx_tb.verilator.vcd

verilator_popcnt6_tb:
	make -C tb/popcnt6 build/popcnt6_tb.verilator.vcd

verilator_fifo_tb:
	make -C tb/fifo build/fifo_tb.verilator.vcd

verilator_fxcs_tb:
	make -C tb/fxcs build/fxcs_tb.verilator.vcd

# }}} verilator

# {{{ iverilog

iverilog_tbs: iverilog_onehotIdx_tb
iverilog_tbs: iverilog_popcnt6_tb
iverilog_tbs: iverilog_fxcs_tb
iverilog_tbs: iverilog_usbFullSpeedPackets_tb
iverilog_tbs: iverilog_usbFullSpeedTransactions_tb
#iverilog_tbs: iverilog_usbFullSpeedSerial_tb
#iverilog_tbs: iverilog_VGWM_usbSerialEchoer_tb

iverilog_onehotIdx_tb:
	make -C tb/onehotIdx build/onehotIdx_tb.iverilog.vcd

iverilog_popcnt6_tb:
	make -C tb/popcnt6 build/popcnt6_tb.iverilog.vcd

iverilog_fxcs_tb:
	make -C tb/fxcs build/fxcs_tb.iverilog.vcd

iverilog_usbFullSpeedPackets_tb:
	make -C tb/usbFullSpeedPackets build/usbFullSpeedPackets_tb.iverilog.vcd

iverilog_usbFullSpeedTransactions_tb:
	make -C tb/usbFullSpeedTransactions build/usbFullSpeedTransactions_tb.iverilog.vcd

iverilog_usbFullSpeedSerial_tb:
	make -C tb/usbFullSpeedSerial build/usbFullSpeedSerial_tb.iverilog.vcd

iverilog_VGWM_usbSerialEchoer_tb:
	make -C tb/usbFullSpeedSerial build/VGWM_usbSerialEchoer_tb.iverilog.vcd

# }}} iverilog

clean_tbs:
	make -C tb/onehotIdx clean
	make -C tb/popcnt6 clean
	make -C tb/fifo clean
	make -C tb/fxcs clean
	make -C tb/usbFullSpeedPackets clean
	make -C tb/usbFullSpeedTransactions clean
	make -C tb/usbFullSpeedSerial clean
	make -C tb/VGWM_usbSerialEchoer clean

# {{{ projects

projects: probsys0
projects: usbFullSpeedSerial_TinyFPGA-BX
projects: VGWM_usbSerialEchoer_TinyFPGA-BX

probsys0:
	make -C prj/probsys0

usbFullSpeedSerial_TinyFPGA-BX:
	make -C prj/usbFullSpeedSerial_TinyFPGA-BX

VGWM_usbSerialEchoer_TinyFPGA-BX:
	make -C prj/VGWM_usbSerialEchoer_TinyFPGA-BX

clean_projects:
	make -C prj/probsys0 clean
	make -C prj/usbFullSpeedSerial_TinyFPGA-BX clean
	make -C prj/VGWM_usbSerialEchoer_TinyFPGA-BX clean

# }}} projects

clean: clean_tbs clean_projects
