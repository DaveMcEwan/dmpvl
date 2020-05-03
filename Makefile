
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

run_tbs:
	make -C tb/bpRegMem
	make -C tb/fifo
	make -C tb/fxcs
	make -C tb/onehotIdx
	make -C tb/popcnt6
	make -C tb/usbFullSpeedPackets
	make -C tb/usbFullSpeedTransactions

clean_tbs:
	make -C tb/bpRegMem clean
	make -C tb/dividerFsm clean
	make -C tb/fifo clean
	make -C tb/fxcs clean
	make -C tb/onehotIdx clean
	make -C tb/popcnt6 clean
	make -C tb/usbFullSpeedPackets clean
	make -C tb/usbFullSpeedTransactions clean
	make -C tb/usbFullSpeedSerial clean
	make -C tb/VGWM_usbSerialEchoer clean
	make -C tb/usbfsSerialEchoer clean

build_projects:
	make -C prj/probsys0
	make -C prj/VGWM_usbSerialEchoer_TinyFPGA-BX
	make -C prj/usbFullSpeedSerial_TinyFPGA-BX
	make -C prj/usbfsSerialEchoer_TinyFPGA-BX
	make -C prj/usbfsBpRegMem_TinyFPGA-BX
	make -C prj/usbfsXoroshiro_TinyFPGA-BX

clean_projects:
	make -C prj/probsys0 clean
	make -C prj/usbFullSpeedSerial_TinyFPGA-BX clean
	make -C prj/VGWM_usbSerialEchoer_TinyFPGA-BX clean
	make -C prj/usbfsSerialEchoer_TinyFPGA-BX clean
	make -C prj/usbfsBpRegMem_TinyFPGA-BX clean
	make -C prj/usbfsXoroshiro_TinyFPGA-BX clean

clean: clean_tbs clean_projects
