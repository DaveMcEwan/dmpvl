
source ../../tcl/vivado-preSynth.tcl

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
    ${dirHdl}/fifoW1R1.sv \
    ${dirHdl}/fxcs.sv \
    ${dirHdl}/logdropWindow.sv \
    ${dirHdl}/mssbIdx.sv \
    ${dirHdl}/onehotIdx.sv \
    ${dirHdl}/prngXoshiro128p.sv \
    ${dirHdl}/strobe.sv \
    ${dirHdl}/pushbutton.sv \
    ${dirHdl}/pwm.sv \
    ${dirHdl}/dividerFsm.sv \
    ${dirHdl}/corrCountRect.sv \
    ${dirHdl}/corrCountLogdrop.sv \
    ${dirHdl}/xbar.sv

  # Project-specific HDL.
  add_files \
    pll48.sv \
    correlator.sv \
    bpReg.sv \
    bpCorrelator.sv \
    usbfsBpCorrelator.sv \
    top.sv
} else {
  # Top-level HDL.
  read_verilog -sv \
    usbfsBpCorrelator.stub.sv \
    ${dirHdl}/fpgaReset.sv \
    pll48.sv \
    top.sv

  # EDIF produced by yosys synthesis.
  read_edif ${dirBuild}/usbfsBpCorrelator.edif
}

set_property file_type "Verilog Header" [get_files -regexp .*\.svh]
check_syntax

# Read in constraints.
read_xdc vc707.xdc

# Synthesize design.
synth_design -part ${part} -top top -include_dirs ${dirHdl}
#  -verilog_define VC707_FMC1_XM105=1 -verilog_define VC707_LED=1

# NOTE: The clock period only needs to be less than 20.833ns.
# The actual clock speed at runtime is set by the PLL settings.
# Synthesizing with a lower value less just means the logic *could* function at
# higher frequencies.
create_clock -name clk48MHz -period 4 [get_nets clk_48MHz]
set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CFGBVS GND [current_design]

source ../../tcl/vivado-postSynth.tcl

