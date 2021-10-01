
PRS =
PRS += paper/BoringFlops
PRS += paper/Foo
PRS += paper/LOD19_12p
PRS += slideset/CorrelatorOverview_0h30m

default: clean all

.PHONY: all
all:
	$(foreach p,$(PRS),cd $(PWD)/$(p) && make;)

.PHONY: clean
clean:
	$(foreach p,$(PRS),cd $(PWD)/$(p) && make clean;)

