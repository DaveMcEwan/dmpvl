
PRS =
PRS += slideset/CorrelatorOverview_0h30m
PRS += paper/LOD19_12p

default: clean all

.PHONY: all
all:
	$(foreach p,$(PRS),cd $(PWD)/$(p) && make;)

.PHONY: clean
clean:
	$(foreach p,$(PRS),cd $(PWD)/$(p) && make clean;)

