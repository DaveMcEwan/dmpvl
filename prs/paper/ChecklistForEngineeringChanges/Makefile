
DOC := ChecklistForEngineeringChanges.pdf
DOC += CondensedChecklistForEngineeringChanges.pdf

.PHONY: default
default: ${DOC}

%.pdf: %.md template.latex
	@pandoc --version
	pandoc --template=template.latex -M pagestyle=empty -i $*.md -o $@

.PHONY: clean
clean:
	rm -f $(DOC)
