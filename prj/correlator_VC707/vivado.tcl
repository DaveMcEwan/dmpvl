
# getopt() usage:
#   Option with default value:
#     getopt argv <shName> <tclName> <defaultValue>
#   OR
#   Boolean flag:
#     set <tclName> [getopt argv <shName>]
#   E.g.
#     $ vivado -mode tcl -tclargs --foo 123 -a
#       % getopt argv --foo abc 456
#       % puts $abc                     --> "123"
#       % getopt argv --bar xyz 789
#       % puts $xyz                     --> "789"
#       % set $boolA [getopt argv a]
#       % puts $boolA                   --> "1"
#       % set $boolB [getopt argv b]
#       % puts $boolB                   --> "0"
# https://wiki.tcl-lang.org/page/getopt
proc getopt {_argv name {_var ""} {default ""}} {
  upvar 1 $_argv argv $_var var
  set pos [lsearch -regexp $argv ^$name]
  if {$pos>=0} {
    set to $pos
    if {$_var ne ""} {
      set var [lindex $argv [incr to]]
    }
    set argv [lreplace $argv $pos $to]
    return 1
  } else {
    if {[llength [info level 0]] == 5} {set var $default}
      return 0
  }
}

getopt argv --report        REPORT      1
getopt argv --checkpoint    CHECKPOINT  1
getopt argv --netlist       NETLIST     1
getopt argv --synth_yosys   SYNTH_YOSYS 0

# AC701 (Artix-7)
#set part "xc7a200tfbg676-2"

# KC705 (Kintex-7)
#set part "xc7k325tffg900-2"

# KCU1500 (Kintex UltraScale)
#set part "xcku115-flvb2104-2-e"

# KCU116 (Kintex UltraScale+)
#set part "xcku5p-ffvb676-2-e"

# VC707 (Virtex-7)
#set part "xc7vx485tffg1157-1"
set part "xc7vx485tffg1761-2"

# VCU108 (Virtex UltraScale)
#set part "xcvu095-ffva2104-2-e"

# VCU118 (Virtex UltraScale+)
#set part "xcvu9p-flga2104-2L-e"

# ZC702 (Zynq)
#set part "xc7z020clg484-1"

# ZCU102 (Zynq UltraScale+)
#set part "xczu9eg-ffvb1156-2-i"

set projname "correlator"
set dirHdl "../../hdl"
set dirBuild "build"
set dirRpt "${dirBuild}/rpt"

file mkdir ${dirBuild}
file mkdir ${dirRpt}


# Untracked (non version-controlled) config should be in here.
if [ file exists untracked.tcl ] {
    source untracked.tcl
}

# Header files.
add_files \
  ${dirHdl}/asrt.svh \
  ${dirHdl}/dff.svh \
  ${dirHdl}/misc.svh \
  ${dirHdl}/usbSpec.svh
set_property is_global_include true [get_files -regexp .*\.svh]

if {$SYNTH_YOSYS == 0} {
  # Generic HDL, used by other projects.
  add_files \
    ${dirHdl}/fpgaReset.sv \
    ${dirHdl}/usbfsPktRx.sv \
    ${dirHdl}/usbfsPktTx.sv \
    ${dirHdl}/usbfsTxn.sv \
    ${dirHdl}/usbfsEndpRx.sv \
    ${dirHdl}/usbfsEndpTx.sv \
    ${dirHdl}/usbfsEndpCtrlSerial.sv \
    ${dirHdl}/usbfsSerial.sv \
    ${dirHdl}/fifo.sv \
    ${dirHdl}/fxcs.sv \
    ${dirHdl}/logdropWindow.sv \
    ${dirHdl}/mssbIdx.sv \
    ${dirHdl}/onehotIdx.sv \
    ${dirHdl}/prngXoshiro128p.sv \
    ${dirHdl}/strobe.sv \
    ${dirHdl}/pwm.sv \
    ${dirHdl}/dividerFsm.sv \
    ${dirHdl}/corrCountRect.sv \
    ${dirHdl}/corrCountLogdrop.sv

  # Project-specific HDL.
  add_files \
    pll48.sv \
    correlator.sv \
    bpReg.sv \
    usbfsBpCorrelator.sv \
    top.sv
} else {
  # Generic HDL, used by other projects.
  read_verilog -sv \
    ${dirHdl}/fpgaReset.sv \
    ${dirHdl}/usbfsPktRx.sv \
    ${dirHdl}/usbfsPktTx.sv \
    ${dirHdl}/usbfsTxn.sv \
    ${dirHdl}/usbfsEndpRx.sv \
    ${dirHdl}/usbfsEndpTx.sv \
    ${dirHdl}/usbfsEndpCtrlSerial.sv \
    ${dirHdl}/usbfsSerial.sv \
    ${dirHdl}/fifo.sv

  # Top-level HDL.
  read_verilog -sv \
    pll48.sv \
    usbfsBpCorrelator.sv \
    top.sv

  # Structural verilog netlist produced by yosys synthesis.
  read_verilog -sv ${dirBuild}/correlator.yosys.v
}

set_property file_type "Verilog Header" [get_files -regexp .*\.svh]
check_syntax

# Read in constraints.
read_xdc vc707.xdc

# Synthesize design.
# NOTE: The clock period only needs to be less than 20.833ns.
# The actual clock speed at runtime is set by the PLL settings.
# Synthesizing with a lower value less just means the logic *could* function at
# higher frequencies.
synth_design -part ${part} -top top -include_dirs ${dirHdl}
create_clock -name clk48MHz -period 4 [get_nets clk_48MHz]
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CFGBVS GND [current_design]
if $CHECKPOINT {
  write_checkpoint -force ${dirBuild}/synth.dcp
}
if $REPORT {
  report_timing_summary   -file ${dirRpt}/synth_timing_summary.rpt
  report_power            -file ${dirRpt}/synth_power.rpt
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
  report_power                -file ${dirRpt}/route_power.rpt
  report_drc                  -file ${dirRpt}/route_drc.rpt
}

# Write out netlist and constraints.
if $NETLIST {
  write_verilog -force ${dirBuild}/netlist.v
  write_xdc -no_fixed_only -force ${dirBuild}/impl.v
}

# Write out a bitstream.
write_bitstream -force ${dirBuild}/${projname}.bit

