
# Read in a CSV file specified by $(CSV) and provide variables CSV_KEYS,
# N_CSV_KEYS, CSV_ROWS, and N_CSV_ROWS.
# NOTE: Supports a single CSV file per makefile.
CSV ?= all.csv

# Lines beginning with # are ignored as comments.
# Blank lines are ignored.
CSV_LINEPARSE := grep -vE "(^\w*$$|^\\\#)"

# Columns in the CSV file may be separated with a comma, tab(s), space(s), or
# any combination of these characters.
CSV_COLPARSE := sed -E 's/(,\s*|\s+)/,/g'

# CSV_KEYS is a space-separated list of column heading names, taken from the
# first non-comment line in the CSV file.
CSV_KEYS := $(shell $(CSV_LINEPARSE) $(CSV) | head -n1 | $(CSV_COLPARSE) | tr ',' ' ')
N_CSV_KEYS := $(shell echo $(CSV_KEYS) | wc -w)

# CSV_ROWS is a space-separated list of items, each corresponding to a row in
# the CSV file.
# Each row item is a comma-separated list of values corresponding to the CSV
# columns.
CSV_ROWS := $(shell $(CSV_LINEPARSE) $(CSV) | tail -n+2 | $(CSV_COLPARSE))
N_CSV_ROWS := $(shell echo $(CSV_ROWS) | wc -w)

# Callable macro to map each row in CSV to a template.
# Use like $(call CSV_ROWMAP,<csv row>,<template using $KEY and $VALUE>)
#   E.g. $(call CSV_ROWMAP,$*,-D$$KEY=$$VALUE)
# NOTE: Depends on Bash syntax. Csh could be supported with ifdef in future.
CSV_ROWMAP = \
	$(shell for i in $$(seq 1 $(N_CSV_KEYS)); do \
		KEY=$$(echo $(CSV_KEYS) | cut -d' ' -f$$i); \
		VALUE=$$(echo $(1) | cut -d',' -f$$i); \
		echo $(2); \
  done)

# Convenience templates.
# Map each row in CSV to a preprocessor define (-Dkey=value).
CSV_ROWMAP_CFLAGDEFINE ?= -D$$KEY=$$VALUE

