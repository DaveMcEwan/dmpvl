
# Prerequisites:
#   https://github.com/dalance/svlint
#   https://github.com/DaveMcEwan/svlint-rulesets
#   https://github.com/verilator/verilator
#   module load mentor/questasim/2022.3
#   module load cadence/xcelium/22.03.004
#   module load synopsys/vcs/2021.09-sp2-2
#   module use --append /pro/sig_research/dddTools/work/aade/linttools/Modules/modulefiles
#   module load linttools/recommended_iverilog

DOC := ParameterDatatypes.pdf
BASENAME := $(basename ${DOC})
TOP := ${BASENAME}.sv

.PHONY: default
default: ${DOC}
default: svlint-parseonly
default: verilator-lint
default: QUESTA.rpt
#default: RIVIERA.rpt
#default: VCS.rpt
default: XCELIUM.rpt
default: VERILATOR.rpt

%.pdf: %.md template.latex
	@pandoc --version
	pandoc --template=template.latex -i $*.md -o $@

.PHONY: svlint-parseonly
svlint-parseonly: ${TOP}
	@svlint --version
	svlint-parseonly ${TOP}

.PHONY: verilator-lint
verilator-lint: ${TOP}
	@verilator --version
	verilator -lint-only ${TOP}

# NOTE: Warning 2605 is for modules without signal ports, and it's suppressed
# because signal ports are not applicable to this paper.
QUESTA.rpt: ${TOP}
	@vlog -version
	vlog -sv17compat -lint \
		-suppress 2605 \
		+define+QUESTA \
		${TOP}
	vsim -lib work work.parent \
		-c -do "run -all; quit -f" \
		-appendlog -l qverilog.log \
		-vopt

RIVIERA.rpt: ${TOP}
	@ -version
	vlib work
	vlib -sv \
		+define+RIVIERA \
		${TOP}
	vsim -c -do "vsim +access+r; run -all; exit"

VCS.rpt: ${TOP}
	vcs -V \
		-sverilog +lint=all -assert svaext \
		+define+VCS \
		${TOP}

XCELIUM.rpt: ${TOP}
	@xrun -version
	xrun -sv \
		-disable_sem2009 \
		-define XCELIUM \
		${TOP}

# NOTE: Icarus Verilog doesn't support IEEE1800-2017.
# As of 2022-08-29, Icarus/Iverilog is lacking support for too many things to
# be worth using for comparison.
# - Structure assignment patterns
# - Unpacked array literals (related to assignment patterns)
# - $typename on a type identifier, rather than a data identifier
# - Streaming concatenation operater
# - Set membership (`inside` keyword)
${BASENAME}.vvp: ${TOP}
	iverilog -v \
		-g2012 \
		-DIVERILOG \
		${TOP}
IVERILOG.rpt: ${BASENAME}.vvp
	time vvp $^

VERILATOR_MAKEFILE := obj_dir/V${BASENAME}.mk
VERILATOR_EXECUTABLE := obj_dir/V${BASENAME}
${VERILATOR_MAKEFILE}: ${TOP}
	@verilator --version
	verilator \
		--language 1800-2017 \
		--trace --cc --exe \
		-CFLAGS -I../../../../verif/ \
		verilator_main.cc \
		${TOP}
${VERILATOR_EXECUTABLE}: ${VERILATOR_MAKEFILE}
	make -j -C obj_dir -f V${BASENAME}.mk V${BASENAME}
VERILATOR.rpt: ${VERILATOR_EXECUTABLE}
	time ${VERILATOR_EXECUTABLE}

.PHONY: clean
clean:
	rm -f $(DOC)
	rm -f *.rpt
	rm -f *.log
	rm -rf work/
	rm -rf xcelium.d/
	rm -f xrun.*
	rm -f xm*.*
	rm -rf obj_dir/
