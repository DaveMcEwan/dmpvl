
CONSTRAINTS ?= $(shell ls *.xdc)

VIVADO_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
VIVADO_FLAGS += --synth_yosys $(SYNTH_YOSYS)

BITFILE ?= $(BUILD)/$(PRJ).bit
SYNTH_YOSYS ?= 0
ifneq ($(SYNTH_YOSYS), 0)
$(BITFILE): $(BUILD)/$(YOSYS_TOP).edif
endif
$(BITFILE): $(VIVADO_SRC) $(CONSTRAINTS) vivado-synth.tcl
	vivado -mode batch -source vivado-synth.tcl \
		-tclargs --prj $(PRJ) --part $(PART) --dirBuild $(BUILD) \
			$(VIVADO_FLAGS)

synth: $(BITFILE)
.PHONY: synth

# Yosys can optionally be used to synth most of a netlist.
YOSYS_SRC ?= $(SRC_SINGLEHIER) $(SRC_MULTIHIER)
YOSYS_INCDIRS ?= $(INCDIRS)
YOSYS_TOP ?= $(PRJ)
synth_yosys: $(BUILD)/$(YOSYS_TOP).edif
%.edif: $(YOSYS_SRC)
	mkdir -p $(BUILD)
	yosys -q \
		-l $*.yosys.log \
		-p 'read_verilog -sv $(addprefix -I,$(YOSYS_INCDIRS)) $^' \
		-p 'synth_xilinx -top $(YOSYS_TOP) -edif $*.edif' \
		-p 'flatten' \
		-p 'write_verilog $*.yosys.v'

VIVADO_SIGNOFF ?= signoffVivado.regex
# NOTE: lineFilter is bundled with dmppl.
#		Setup venv for Python 3.6+ ...
#		git clone https://github.com/DaveMcEwan/dmppl.git
#		pip install -e ./dmppl
$(BUILD)/vivado.warnings: $(BITFILE) $(VIVADO_SIGNOFF)
	grep -n WARNING vivado.log | lineFilter $(VIVADO_SIGNOFF) > $@

signoff: $(BUILD)/vivado.warnings
	! test -s $<
.PHONY: signoff

prog:
	vivado -mode batch -source ../../tcl/vivado-program.tcl \
		-tclargs --part $(PART) --bitstream $(BITFILE)
.PHONY: prog

CLEAN_PATHS += .Xil
CLEAN_PATHS += .cache
CLEAN_PATHS += usage_statistics*
CLEAN_PATHS += vivado*.log vivado*.jou
CLEAN_PATHS += webtalk*.log webtalk*.jou

