
# Begin work with something like:
#		sudo make -f tools.mk apt_prereqs
#		make -f tools.mk
#		export PATH=$PWD/tools/bin:$PATH
# NOTE: Specific commits are just the latest ones I've tested.
TOOLS := $(PWD)/tools
TOOLBUILD := $(PWD)/tools/build
N_JOBS ?= 6

default: tools

# Debian/Ubuntu based systems only.
# NOTE: This may need tweaking, depending on the system state.
apt_prereqs:
		apt install \
			autoconf \
			build-essential \
			clang \
			bison \
			flex \
			gperf \
			libreadline-dev \
			gawk \
			tcl-dev \
			libffi-dev \
			git \
			graphviz \
			xdot \
			pkg-config \
			python \
			python3 \
			python3-dev \
			libftdi-dev \
			qt5-default \
			python3-dev \
			libboost-all-dev \
			cmake \
			zlib1g-dev \
			libeigen3-dev \
			time


tools: iverilog
tools: verilator
tools: gtkwave
tools: icestorm
tools: yosys
tools: arachne-pnr
tools: nextpnr-ice40
tools: tinyprog

BUILD_IVERILOG := $(TOOLBUILD)/iverilog
URL_IVERILOG := https://github.com/steveicarus/iverilog.git
COMMIT_IVERILOG := 7f95abc6ab6b9428cf2e5c3c2360eace1cfc6be3
iverilog:
	mkdir -p $(BUILD_IVERILOG)
	git clone $(URL_IVERILOG) $(BUILD_IVERILOG)
	cd $(BUILD_IVERILOG); git checkout $(COMMIT_IVERILOG)
	cd $(BUILD_IVERILOG); sh autoconf.sh
	cd $(BUILD_IVERILOG); ./configure --prefix=$(TOOLS)
	cd $(BUILD_IVERILOG); make -j$(N_JOBS)
	cd $(BUILD_IVERILOG); make check
	cd $(BUILD_IVERILOG); make install

BUILD_VERILATOR := $(TOOLBUILD)/verilator
URL_VERILATOR := https://github.com/verilator/verilator.git
#COMMIT_VERILATOR := stable
COMMIT_VERILATOR := 6f52208b6817975cf1e2479c8646f979dfd94ed9
verilator:
	mkdir -p $(BUILD_VERILATOR)
	git clone $(URL_VERILATOR) $(BUILD_VERILATOR)
	cd $(BUILD_VERILATOR); git checkout $(COMMIT_VERILATOR)
	cd $(BUILD_VERILATOR); autoconf
	cd $(BUILD_VERILATOR); ./configure --prefix=$(TOOLS)
	cd $(BUILD_VERILATOR); make -j$(N_JOBS)
	cd $(BUILD_VERILATOR); make install

# GtkWave is stable enough in the main repos and doesn't appear to be actively
# developed (though doesn't need to be).
# NOTE: v3.3.36 (2017) is known to be usable, newest at time of writing.
# TODO?: Tony Bybell appears to be moving the project to Github which will make
# it easier to track specific versions.
gtkwave:
	apt install gtkwave

# Documentation for building icestorm, yosys, arachne-pnr:
#		http://www.clifford.at/icestorm/
BUILD_ICESTORM := $(TOOLBUILD)/icestorm
URL_ICESTORM := https://github.com/cliffordwolf/icestorm.git
COMMIT_ICESTORM := 0ec00d892a91cc68e45479b46161f649caea2933
icestorm:
	mkdir -p $(BUILD_ICESTORM)
	git clone $(URL_ICESTORM) $(BUILD_ICESTORM)
	cd $(BUILD_ICESTORM); git checkout $(COMMIT_ICESTORM)
	cd $(BUILD_ICESTORM); make PREFIX=$(TOOLS)
	cd $(BUILD_ICESTORM); make install PREFIX=$(TOOLS)

BUILD_YOSYS := $(TOOLBUILD)/yosys
URL_YOSYS := https://github.com/YosysHQ/yosys.git
COMMIT_YOSYS := 7e5602ad17b20f14e56fc4c64198ca2d576917df
yosys:
	mkdir -p $(BUILD_YOSYS)
	git clone $(URL_YOSYS) $(BUILD_YOSYS)
	cd $(BUILD_YOSYS); git checkout $(COMMIT_YOSYS)
	cd $(BUILD_YOSYS); make -j$(N_JOBS) PREFIX=$(TOOLS)
	cd $(BUILD_YOSYS); make install PREFIX=$(TOOLS)

# NOTE: Both place and route tools (arachne-pnr, nextpnr) convert the icestorm
# text chip databases into the respective PNR binary chip databases during
# build.
# Always rebuild the PNR tools after updating icestorm.

# NOTE: arachne-pnr is superceeded by nextpnr and is no longer being actively
# developed.
# However, it can produce results more quickly so is still used.
BUILD_ARACHNE := $(TOOLBUILD)/arachne-pnr
URL_ARACHNE := https://github.com/YosysHQ/arachne-pnr.git
COMMIT_ARACHNE := c40fb2289952f4f120cc10a5a4c82a6fb88442dc
arachne-pnr:
	mkdir -p $(BUILD_ARACHNE)
	git clone $(URL_ARACHNE) $(BUILD_ARACHNE)
	cd $(BUILD_ARACHNE); git checkout $(COMMIT_ARACHNE)
	cd $(BUILD_ARACHNE); make -j$(N_JOBS) PREFIX=$(TOOLS)
	cd $(BUILD_ARACHNE); make install PREFIX=$(TOOLS)

BUILD_NEXTPNRICE40 := $(TOOLBUILD)/nextpnr-ice40
URL_NEXTPNRICE40 := https://github.com/YosysHQ/nextpnr.git
COMMIT_NEXTPNRICE40 := dd7f7a53bd5ae51ca3ff172b6e4de65128ab8a6d
nextpnr-ice40:
	mkdir -p $(BUILD_NEXTPNRICE40)
	git clone $(URL_NEXTPNRICE40) $(BUILD_NEXTPNRICE40)
	cd $(BUILD_NEXTPNRICE40); git checkout $(COMMIT_NEXTPNRICE40)
	cd $(BUILD_NEXTPNRICE40); cmake \
		-DARCH=ice40 \
		-DCMAKE_INSTALL_PREFIX=$(TOOLS) \
		-DICEBOX_ROOT=$(TOOLS)/share/icebox .
	cd $(BUILD_NEXTPNRICE40); make -j$(N_JOBS)
	cd $(BUILD_NEXTPNRICE40); make install

# NOTE: Take care to use the correct venv, perhaps adding the line
# `source /path/to/myvenv/bin/activate` to your bashrc.
tinyprog:
	python3 -m pip install tinyprog==1.0.21

