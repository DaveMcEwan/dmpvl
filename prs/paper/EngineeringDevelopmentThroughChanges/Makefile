
DOC := EngineeringDevelopmentThroughChanges.pdf

.PHONY: default
default: ${DOC}

%.pdf: %.md
	@pandoc --version
	pandoc -i $*.md -o $@

.PHONY: clean
clean:
	rm -f $(DOC)
