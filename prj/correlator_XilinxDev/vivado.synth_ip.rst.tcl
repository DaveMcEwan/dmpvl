
set ipname "rst_m"

set vlnv "xilinx.com:ip:proc_sys_reset:5.0"

create_ip -dir ${dir_ip} -vlnv ${vlnv} -module_name ${ipname}

set_property -dict [ list \
    CONFIG.C_EXT_RST_WIDTH {1} \
    CONFIG.C_AUX_RST_WIDTH {1} \
    CONFIG.C_EXT_RESET_HIGH {1} \
    CONFIG.C_AUX_RESET_HIGH {1} \
] [get_ips ${ipname}]

synth_ip [ get_ips ${ipname} ]

