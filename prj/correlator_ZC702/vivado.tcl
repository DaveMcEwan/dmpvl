
set REPORT 1
set CHECKPOINT 1
set NETLIST 1

# zc702 part
set part "xc7z020clg484-1"

set projname "correlator"
set dir_xdc "xdc"
set dir_hdl "../../hdl"
set dir_bld "build"
set dir_rpt "${dir_bld}/rpt"
set dir_ip  "${dir_bld}/ip"


set rpt_post_route "${dir_rpt}/route_"

# Untracked (non version-controlled) config should be in here.
if [ file exists untracked.tcl ] {
    source untracked.tcl
}

# Build IP from catalog.
if [ file exists ${dir_bld}/synth_ip.DONE ] {
  read_checkpoint ${dir_bld}/ip/ps7_m/ps7_m.dcp
  read_checkpoint ${dir_bld}/ip/rst_m/rst_m.dcp
} else {
  set_part ${part}
  source vivado.synth_ip.ps7.tcl
  source vivado.synth_ip.rst.tcl
  exec touch ${dir_bld}/synth_ip.DONE
}

# Read in all source files.
read_verilog \
  ${dir_hdl}/fpgaReset.sv \
  ${dir_hdl}/usbfsPktRx.sv \
  ${dir_hdl}/usbfsPktTx.sv \
  ${dir_hdl}/usbfsTxn.sv \
  ${dir_hdl}/usbfsEndpRx.sv \
  ${dir_hdl}/usbfsEndpTx.sv \
  ${dir_hdl}/usbfsEndpCtrlSerial.sv \
  ${dir_hdl}/usbfsSerial.sv \
  ${dir_hdl}/fifo.sv \
  ${dir_hdl}/fxcs.sv \
  ${dir_hdl}/logdropWindow.sv \
  ${dir_hdl}/mssbIdx.sv \
  ${dir_hdl}/onehotIdx.sv \
  ${dir_hdl}/prngXoshiro128p.sv \
  ${dir_hdl}/strobe.sv \
  ${dir_hdl}/pwm.sv \
  ${dir_hdl}/dividerFsm.sv \
  ${dir_hdl}/corrCountRect.sv \
  ${dir_hdl}/corrCountLogdrop.sv \
  ${dir_bld}/pll48.sv \
  correlator.sv \
  bpReg.sv \
  top.sv

# Read in constraints.
read_xdc \
  ${dir_xdc}/clkrst.xdc \
  ${dir_xdc}/ddr.xdc \
  ${dir_xdc}/mio.xdc \
  ${dir_xdc}/o_led.xdc

# Synthesize design.
synth_design -part ${part} -top top_m
if $CHECKPOINT {
  write_checkpoint -force ${dir_bld}/synth.dcp
}
if $REPORT {
  report_timing_summary   -file ${dir_rpt}/synth_timing_summary.rpt
  report_power            -file ${dir_rpt}/synth_power.rpt
}

# Optimize, place design.
opt_design
place_design
phys_opt_design
if $CHECKPOINT {
  write_checkpoint -force ${dir_bld}/place.dcp
}

# Route design.
route_design
if $CHECKPOINT {
  write_checkpoint -force ${dir_bld}/route.dcp
}
if $REPORT {
  report_timing -sort_by group -max_paths 100 -path_type summary \
                              -file ${dir_rpt}/route_timing.rpt
  report_timing_summary       -file ${dir_rpt}/route_timing_summary.rpt
  report_clock_utilization    -file ${dir_rpt}/route_clock_utilization.rpt
  report_utilization          -file ${dir_rpt}/route_utilization.rpt
  report_power                -file ${dir_rpt}/route_power.rpt
  report_drc                  -file ${dir_rpt}/route_drc.rpt
}

# Write out netlist and constraints.
if $NETLIST {
  write_verilog -force ${dir_bld}/netlist.v
  write_xdc -no_fixed_only -force ${dir_bld}/impl.v
}

# Write out a bitstream.
write_bitstream -force ${dir_bld}/${projname}.bit

