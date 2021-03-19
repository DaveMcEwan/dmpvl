
# Setup venv for Python 3.6+ ...
# pip install wavedrom
WAVEDROM_JSON := $(shell ls *.wavedrom.json)
WAVEDROM_SVG := $(WAVEDROM_JSON:.wavedrom.json=.wavedrom.svg)
wavedrom: $(WAVEDROM_SVG)
.PHONY: wavedrom

%.wavedrom.svg: %.wavedrom.json
	wavedrompy -i $^ -s $@

CLEAN_PATHS += *.wavedrom.svg

.SECONDARY:

