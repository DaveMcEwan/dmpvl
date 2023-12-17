
PDF ?= slides.pdf
SRC_MD ?= $(shell find . -maxdepth 1 -regex '\./[0-9]+.*\.md' | sort)

default: ${PDF}

PANDOC_FLAGS := -t beamer
PANDOC_FLAGS += --variable=colorlinks
PANDOC_FLAGS += --template=beamer.tex
#PANDOC_FLAGS += --metadata="date:$(shell date '+%A %Y-%m-%d')"
PANDOC_FLAGS += --metadata=theme:Custom
PANDOC_FLAGS += --metadata=colortheme:Custom

ifdef CLASSIFICATION
PANDOC_FLAGS += --variable=copyright
#PANDOC_FLAGS += --variable="institute:MyInstitute"
# CLASSIFICATION must be in {INTERNAL, CONFIDENTIAL, SECRET} as anything else
# implies PUBLIC.
PANDOC_FLAGS += --variable="classification:${CLASSIFICATION}"
endif
${PDF}: ${SRC_MD}
	pandoc ${PANDOC_FLAGS} ${SRC_MD} -o ${PDF}

# For each source file containing shell commands, create the name of a target
# file which can be sourced.
RE_SHCMD := '^[ ]*- `.*`$$'
SRC_MD_SHCMD := $(shell grep -El ${RE_SHCMD} ${SRC_MD} | xargs -I{} basename {})
SH := $(addprefix source/,$(subst .md,.sh,${SRC_MD_SHCMD}))

sh: ${SH}

# Extract commands into files which can be sourced, which is a bit more
# convenient than typing during a presentation.
# Commands are always formatted one per line as any-level list items which are
# delimited by backticks, with nothing else on the line.
source/%.sh:
	grep -E ${RE_SHCMD} $*.md | \
		sed -r 's/.*`(.*)`.*/\1/' > $@

.PHONY: clean
clean:
	rm ${PDF}

