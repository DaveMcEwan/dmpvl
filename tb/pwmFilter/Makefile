BUILD ?= ./build

analyse:
	mkdir -p $(BUILD)
	ngspice pwmFilter.cir

plot:
	plotCsv --pdf --skiprows=1 --delimiter=' ' --markers='' \
		--ylim='-0.2,2.0' \
		-o $(BUILD)/pwmFilter.tran $(BUILD)/pwmFilter.tran.txt

clean:
	rm -rf $(BUILD)
