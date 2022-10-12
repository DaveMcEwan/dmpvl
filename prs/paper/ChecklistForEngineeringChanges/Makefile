
DOC := ChecklistForEngineeringChanges.pdf

.PHONY: default
default: ${DOC}

%.pdf: %.md template.latex
	@pandoc --version
	pandoc --template=template.latex -i $*.md -o $@

.PHONY: clean
clean:
	rm -f $(DOC)
