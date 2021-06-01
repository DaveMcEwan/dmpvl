
# Default recipe here should try to build everything by running the default
# recipe in each relevant subdirectory.
# NOTE: Long running experiments like multipnr should not be run.
CSET := '\e[7m\e[32m'
CUNSET := '\e[27m\e[39m'
default: check_hdl check_verif run_tbs build_projects
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

# NOTE: Not compatible with "make -C" because $(TB) is defined by $(PWD).
run_tbs:
	cd tb/bpRegMem; make
	cd tb/dividerFsm; make
	cd tb/fifoW1R1; make
	cd tb/fifoScoreboards; make
	cd tb/fxcs; make
	cd tb/logdropWindow; make
	cd tb/onehotIdx; make
	cd tb/praxi; make
	cd tb/popcnt6; make
	cd tb/usbFullSpeedPackets; make
	cd tb/usbFullSpeedTransactions; make

clean_tbs:
	make -C tb/bpRegMem clean
	make -C tb/dividerFsm clean
	make -C tb/fifoW1R1 clean
	make -C tb/fifoScoreboards clean
	make -C tb/fxcs clean
	make -C tb/logdropWindow clean
	make -C tb/onehotIdx clean
	make -C tb/popcnt6 clean
	make -C tb/praxi clean
	make -C tb/usbFullSpeedPackets clean
	make -C tb/usbFullSpeedTransactions clean
	make -C tb/usbFullSpeedSerial clean
	make -C tb/VGWM_usbSerialEchoer clean
	make -C tb/usbfsSerialEchoer clean

# Some projects may be allowed to fail when timing is known to be tight and
# subject to randomization.
build_projects:
	make -C prj/VGWM_usbSerialEchoer_TinyFPGA-BX
	make -C prj/usbFullSpeedSerial_TinyFPGA-BX
	make -C prj/usbfsSerialEchoer_TinyFPGA-BX
	-make -C prj/usbfsBpRegMem_TinyFPGA-BX
	make -C prj/usbfsXoroshiro_TinyFPGA-BX

clean_projects:
	make -C prj/usbFullSpeedSerial_TinyFPGA-BX clean
	make -C prj/VGWM_usbSerialEchoer_TinyFPGA-BX clean
	make -C prj/usbfsSerialEchoer_TinyFPGA-BX clean
	make -C prj/usbfsBpRegMem_TinyFPGA-BX clean
	make -C prj/usbfsXoroshiro_TinyFPGA-BX clean

clean: clean_tbs clean_projects
