#!/usr/bin/env tclsh

set build "build.icecube2"
set edif "top.synplifypro"
set device "iCE40LP8K-CM81"
set tool_options ":edifparser -y pins.pcf"

set sbt_root $::env(SBT_DIR)
append sbt_tcl $sbt_root "/tcl/sbt_backend_synpl.tcl"
source $sbt_tcl

run_sbt_backend_auto $device top $build "" $tool_options $edif

exit
