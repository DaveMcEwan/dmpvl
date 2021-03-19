# Run place-and-route with different seed values to get a distribution of
# timing results.
# NOTE: Use the -j flag to parallelize runs.
# Put all asc,rpt,log files in ./multipnr/<seed>/*.{asc,rpt,log}
# Create a CSV log with these values:
#		seed, nextpnr.log, icetime.rpt, arachne.icetime.rpt


# TinyFPGA-BX
DEVICE ?= lp8k
PACKAGE ?= cm81

PCF ?= pins.pcf
BUILD ?= ./build

N_RUNS ?= 10

# 0 -> Don't bother with arachne-pnr, otherwise do.
MULTIPNR_ARACHNE ?= 0

MULTIPNR_XLIM ?= 35,75
MULTIPNR_YLIM ?= 0,0.25


NUMBERS := $(shell seq 1 $(N_RUNS))
ASC_NEXTPNR := $(addprefix multipnr/,$(addsuffix /nextpnr.asc,$(NUMBERS)))
RPT_NEXTPNR := $(addprefix multipnr/,$(addsuffix /nextpnr.rpt,$(NUMBERS)))
ASC_ARACHNE := $(addprefix multipnr/,$(addsuffix /arachne.asc,$(NUMBERS)))
RPT_ARACHNE := $(addprefix multipnr/,$(addsuffix /arachne.rpt,$(NUMBERS)))


# nextpnr takes JSON
multipnr/%/nextpnr.asc:
	mkdir -p $(@D)
	nextpnr-ice40 -q \
		--$(DEVICE) --package $(PACKAGE) --pcf $(PCF) \
		-l $(@D)/nextpnr.log \
		--seed $* \
		--opt-timing \
		--json $(BUILD)/$(PROJ).yosys.json \
		--asc $@

$(RPT_NEXTPNR): multipnr/%/nextpnr.rpt: multipnr/%/nextpnr.asc
	icetime -d $(DEVICE) -mtr $@ $<


# NOTE: Arachne takes BLIF
$(ASC_ARACHNE): multipnr/%/arachne.asc:
	mkdir -p $(@D)
	-arachne-pnr \
		--device 8k \
		--package $(PACKAGE) \
		--seed $* \
		--pcf-file $(PCF) \
		$(BUILD)/$(PROJ).yosys.blif \
		--output-file $@ 2> $(@D)/arachne.log

$(RPT_ARACHNE): multipnr/%/arachne.rpt: multipnr/%/arachne.asc
	icetime -d $(DEVICE) -mtr $@ $< || \
		echo "Total path delay: 0.0 ns (0.0 MHz)" > $@


multipnr/nextpnr.log.extracted: ${RPT_NEXTPNR}
	for f in multipnr/*/nextpnr.log; do \
		grep --with-filename 'Max frequency for clock' $$f | grep clk_48MHz_ | \
			tail -1 >> multipnr/nextpnr.log.extracted; \
	done

multipnr/nextpnr.rpt.extracted: ${RPT_NEXTPNR}
	grep -H 'Total path delay:' multipnr/*/nextpnr.rpt > \
		multipnr/nextpnr.rpt.extracted

# NOTE: Arachne often fails to finish, so ignore those runs.
multipnr/arachne.rpt.extracted: ${RPT_ARACHNE}
	-grep -H 'Total path delay:' multipnr/*/arachne.rpt > \
		multipnr/arachne.rpt.extracted


multipnr/results.csv.pdf: multipnr/nextpnr.log.extracted
multipnr/results.csv.pdf: multipnr/nextpnr.rpt.extracted
ifneq ($(MULTIPNR_ARACHNE), 0)
multipnr/results.csv.pdf: multipnr/arachne.rpt.extracted
endif
multipnr/results.csv.pdf:
	$(dir $(MK_MULTIPNR))/multipnrPlot.py \
		--xlim=$(MULTIPNR_XLIM) --ylim=$(MULTIPNR_YLIM) \
		--doArachne=$(MULTIPNR_ARACHNE)


multipnr: $(PCF) synth
multipnr: multipnr/results.csv.pdf
.PHONY: multipnr

# NOTE: No CLEAN_PATHS for multipnr because accidentally deleting results is a
# much bigger inconvenience that typing `rm -rf multipnr` when you need to.

