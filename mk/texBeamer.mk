
AUTHOR ?= DaveMcEwan
MAIN ?= main
SRC_TEX := $(shell ls *.tex) $(shell ls shr/tex/*.tex)
SRC_BIB := shr/refs.bib

# All steps of pdflatex.
# NOTE: beamer-times is a Python script included in dmppl.
default: $(MAIN).pdf
	beamer-times main.tex
#	texcount $(shell ls *.tex)

# Single step of pdflatex.
min: $(MAIN).X.log

.PHONY: default min

$(MAIN).pdf: $(MAIN).1.log
#$(MAIN).pdf: $(MAIN).bbl
$(MAIN).pdf: $(MAIN).2.log
#$(MAIN).pdf: $(MAIN).3.log

# If pdflatex fails, then print last 50 lines from logfile before erroring.
$(MAIN).%.log: $(SRC_TEX)
	pdflatex -halt-on-error -file-line-error $(MAIN) > $@ || (tail -n50 $@ && exit 1)

$(MAIN).bbl: $(SRC_BIB) $(MAIN).1.log
	-bibtex -terse $(MAIN)


open:
	xdg-open $(MAIN).pdf
.PHONY: open


# Create a copy for sending to colleagues, and archive ready for publishing
# using the manifest file.
#   make clean release archive
RELEASE := $(AUTHOR)_$(shell basename $$PWD)_$(shell date --iso-8601)

archive: $(MAIN).pdf
	tar -chzvf $(RELEASE).tar.gz \
		$(shell cat manifest | grep -vE '^[[:space:]]*(#|$$)')
.PHONY: archive

release: $(MAIN).pdf
	cp $(MAIN).pdf $(RELEASE).pdf
.PHONY: release

clean:
	rm -f *.log
	rm -f *.aux *.bbl *.blg
	rm -f *.lof *.lot *.toc
	rm -f *.out *.idx
	rm -f *.nav *.snm *.vrb
	rm -f $(MAIN).pdf
.PHONY: clean

