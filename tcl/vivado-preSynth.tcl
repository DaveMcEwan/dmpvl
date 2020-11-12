
# Relative path from point of execution (e.g. dmpvl/prj/correlator_Zedboard/)
# rather than from this file.
source ../../tcl/getopt.tcl
getopt argv --report        REPORT      1
getopt argv --checkpoint    CHECKPOINT  1
getopt argv --netlist       NETLIST     1
getopt argv --synth_yosys   SYNTH_YOSYS 0
getopt argv --part          part        XXX
getopt argv --prj           prj         XXX
getopt argv --dirBuild      dirBuild    "build"

set dirHdl "../../hdl"
set dirRpt "${dirBuild}/rpt"
set dirIp "${dirBuild}/ip"

file mkdir ${dirBuild}
file mkdir ${dirRpt}
file mkdir ${dirIp}

create_project -in_memory -part ${part} ${prj}

# Untracked (non version-controlled) config should be in here.
if [ file exists untracked.tcl ] {
    source untracked.tcl
}
