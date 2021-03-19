
Primary make targets are:
- `lint_foss` - Check source files can be read with FOSS tools (iverilog,
  verilator, yosys).
- `lint_paid` - Check source files can be read with a selection of expensive
  paid tools (Formalpro, HAL, Jaspergold, Modelsim/Questa, Spyglass, VCS,
  Vivado, Xcelium).
- `lint_<tool>` - Check source files with a specific tool.
- `preproc` - Run source files through the Verilator preprocessor.
  Useful to support flows with older toolchains.
- `synth` - Run synthesis tool (yosys, vivado) to generate netlist.
- `pnr` - Place-and-route a synthesized netlist.
- `clean` - Remove all generated files.
- `multipnr` - Use many PnR runs to plot a Probability Density Function of the
  attained FMAX.
  Only the Lattice iCE40 flow (yosys, nextpnr) is currently supported.
- `wavedrom` - Use JSON definitions of waveforms to draw pretty diagrams.
- `signoff` - Run logfile through a regex filter to signoff warnings.
  Currently only supported on vivado projects, because FOSS tools don't emit so
  much noise.
- `prog` - Upload bitstream to a connected FPGA development board.
