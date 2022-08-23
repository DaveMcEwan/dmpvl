#
# Prerequisites:
#   https://github.com/dalance/svlint
#   https://github.com/DaveMcEwan/svlint-rulesets
#   https://github.com/verilator/verilator
#   module load mentor/questasim/2022.3
#   module load cadence/xcelium/22.03.004

DOC := ParameterDatatypes
TOP := example.sv

default: ${DOC}.pdf
default: svlint-parseonly
default: verilator-lint
default: questa-sim
default: xcelium-sim

%.pdf: %.md
	@pandoc --version
	pandoc -i $*.md -o $@

.PHONY: svlint-parseonly
svlint-parseonly:
	@svlint --version
	svlint-parseonly ${TOP}

.PHONY: verilator-lint
verilator-lint:
	@verilator --version
	verilator -lint-only ${TOP}

# NOTE: Warning 2605 is for modules without signal ports, and is suppressed
# because signal ports are not applicable to this paper.
.PHONY: questa-sim
questa-sim:
	@vlog -version
	vlog -sv17compat -lint \
		-suppress 2605 \
		+define+QUESTA \
		${TOP}
	vsim -lib work work.parent \
		-c -do "run -all; quit -f" \
		-appendlog -l qverilog.log \
		-vopt

.PHONY: xcelium-sim
xcelium-sim:
	@xrun -version
	xrun -sv \
		-disable_sem2009 \
		-define XCELIUM \
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
