
# Prerequisites:
#   https://github.com/dalance/svlint
#   https://github.com/DaveMcEwan/svlint-rulesets
#   https://github.com/verilator/verilator
#   module load mentor/questasim/2022.3
#   module load cadence/xcelium/22.03.004
#   module load synopsys/vcs/2021.09-sp2-2

DOC := ParameterDatatypes.pdf
TOP := $(basename ${DOC}).sv

.PHONY: default
default: ${DOC}
default: svlint-parseonly
default: verilator-lint
default: QUESTA.rpt
default: XCELIUM.rpt

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

XCELIUM.rpt: ${TOP}
	@xrun -version
	xrun -sv \
		-disable_sem2009 \
		-define XCELIUM \
		${TOP}

# NOTE: Untested.
VCS.rpt: ${TOP}
	vcs -V \
		-sverilog +lint=all \
		+define+VCS \
		${TOP}

.PHONY: clean
clean:
	rm -f $(DOC).pdf
	rm -f *.rpt
	rm -f *.log
	rm -rf work/
	rm -rf xcelium.d/
	rm -f xrun.*
	rm -f xm*.*
