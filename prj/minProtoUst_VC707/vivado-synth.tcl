
source ../../tcl/vivado-preSynth.tcl

# Files added from UltraSoC delivery using Makefile-generated script.
source ${dirBuild}/vivado-addFiles.tcl
getopt argv --deliveryIncdir deliveryIncdir XXX

add_files \
  ${dirHdl}/asrt.svh \
  ${dirHdl}/dff.svh \
  ${dirHdl}/misc.svh

read_verilog -sv \
  ${dirHdl}/fpgaReset.sv \
  ${dirHdl}/syncBit.sv \
  ${dirHdl}/fifoW1R1.sv \
  ${dirHdl}/fxcs.sv \
  ${dirHdl}/logdropWindow.sv \
  ${dirHdl}/mssbIdx.sv \
  ${dirHdl}/onehotIdx.sv \
  ${dirHdl}/prngXoshiro128p.sv \
  ${dirHdl}/strobe.sv \
  ${dirHdl}/pwm.sv \
  ${dirHdl}/dividerFsm.sv \
  ${dirHdl}/corrCountRect.sv \
  ${dirHdl}/corrCountLogdrop.sv \
  ${dirHdl}/xbar.sv \
  correlator.sv \
  pll.sv \
  top.sv

set_property is_global_include true [get_files -regexp .*\.vh]
set_property is_global_include true [get_files -regexp .*\.svh]
set_property file_type "Verilog Header" [get_files -regexp .*\.vh]
set_property file_type "Verilog Header" [get_files -regexp .*\.svh]
check_syntax

# Read in constraints.
read_xdc vc707.xdc

# Synthesize design.
synth_design -part ${part} -top top \
  -verilog_define SYNTHESIS=1 \
  -verilog_define ust_fpga_c=1 \
  -verilog_define ust_vivado_c=1 \
  -verilog_define ust_use_msg_slice_c=1 \
  -include_dirs ${deliveryIncdir} \
  -include_dirs ${dirHdl}

set_property CONFIG_VOLTAGE 1.8 [current_design]
set_property CFGBVS GND [current_design]

source ../../tcl/vivado-postSynth.tcl

