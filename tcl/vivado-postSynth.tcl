
if $CHECKPOINT {
  write_checkpoint -force ${dirBuild}/synth.dcp
}
if $REPORT {
  report_timing_summary   -file ${dirRpt}/synth_timing_summary.rpt
  report_power -advisory  -file ${dirRpt}/synth_power.rpt
}

# Optimize, place design.
opt_design
place_design
phys_opt_design
if $CHECKPOINT {
  write_checkpoint -force ${dirBuild}/place.dcp
}

# Route design.
route_design
if $CHECKPOINT {
  write_checkpoint -force ${dirBuild}/route.dcp
}
if $REPORT {
  report_timing -sort_by group -max_paths 100 -path_type summary \
                              -file ${dirRpt}/route_timing.rpt
  report_timing_summary       -file ${dirRpt}/route_timing_summary.rpt
  report_clock_utilization    -file ${dirRpt}/route_clock_utilization.rpt
  report_utilization          -file ${dirRpt}/route_utilization.rpt
  report_power -advisory      -file ${dirRpt}/route_power.rpt
  report_drc                  -file ${dirRpt}/route_drc.rpt
}

# Write out netlist and constraints.
if $NETLIST {
  write_verilog -force ${dirBuild}/netlist.v
  write_xdc -no_fixed_only -force ${dirBuild}/constraints.xdc
}

# Write out a bitstream.
write_bitstream -force ${dirBuild}/${prj}.bit

