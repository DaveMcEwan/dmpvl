
AUTHOR ?= DaveMcEwan
MAIN ?= main
SRC_TEX := $(shell ls *.tex) $(shell ls shr/tex/*.tex)
SRC_BIB := shr/refs.bib

# All steps of pdflatex and bibtex.
default: $(MAIN).pdf
	texcount -brief $(shell ls *.tex)
#	texcount $(shell ls *.tex)

# Single step of pdflatex.
min: $(MAIN).X.log
	texcount -brief $(shell ls *.tex | grep -v "$(MAIN)\.tex" | grep -v 'appendix_.*\.tex')

.PHONY: default min

$(MAIN).pdf: $(MAIN).1.log
$(MAIN).pdf: $(MAIN).bbl
$(MAIN).pdf: $(MAIN).2.log
$(MAIN).pdf: $(MAIN).3.log

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


## Command fragment for isolating one word per line of TeX from STDIN.
##   1. Remove comments,
##   2. Replace \gls commands (but not argument) which are one word each,
##   3. Split commands (with argument) appended to words (cite, footnotemark),
##   4. Split into lines by whitespace,
##   5. Remove non-TeX punctuation which may be part of words,
##   6. Convert to lowercase for uniqueness count,
##   7. Remove specific (La)TeX setup and environment commands,
##   8. Remove post-word-argument braces,
##   9. Remove pre-word-argument braces,
##   10. Leave only lines without punctuation.
## NOTE: This is not perfect, especially with preamble (La)TeX, but is "pretty
##   good" for content (La)TeX.
##   More conservative than `detex foo.tex | wc -w`.
#TEXWORDS = \
#	sed -Ee 's/%.*//g' | \
#	sed -Ee 's/\\gls[[:alpha:]]*\{([[:alnum:]]+)\}/\1/g' | \
#	sed -Ee 's/([[:alnum:]]+)\\/\1  \\/g' | \
#	sed -Ee 's/[[:space:]]+/\n/g' | \
#	tr -d "!\"'(),./:;?_\`-" | \
#	tr '[:upper:]' '[:lower:]' | \
#	grep -Ev '\\(begin|.*box|cite|.*depth|end|fref|include.*|input|label|ref|use.*|set.*|.*space|.*style)' | \
#	sed -Ee 's/\}.*//g' | \
#	sed -Ee 's/.*\{//g' | \
#	grep -E '^[[:alpha:]]+[[:alnum:]]*$$'
#
#TEXWORDCOUNT = \
#	echo '$(TEXPATH)' "\t" \
#		$(shell cat $(TEXPATH) | $(TEXWORDS) | wc -l) "\t" \
#		$(shell cat $(TEXPATH) | $(TEXWORDS) | sort | uniq | wc -l);
#
## NOTE: Where possible, use real texcount program instead of this depending
## on this recipe.
#.PHONY: texcount
#texcount:
#	@echo "File\t#Words\t#Unique"
#	@$(foreach TEXPATH,$(shell ls *.tex) *.tex,$(TEXWORDCOUNT))

