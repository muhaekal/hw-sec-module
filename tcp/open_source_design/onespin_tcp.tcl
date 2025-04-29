####################################################
# Copyright(c) LUBIS EDA GmbH, All rights reserved #
# Contact: contact@lubis-eda.com                   #
####################################################

# TCL-script for OneSpin (Siemens EDA)

# Change working directory to the directory of the script
set SCRIPT_LOCATION [file dirname [file normalize [info script]]]
cd $SCRIPT_LOCATION

# Restart
set_mode setup
delete_design -both
remove_server -all

# Change style from name/name to name.name
set_session_option -naming_style sv

# Load the file(s) by using the SystemVerilog standard SV2012
read_verilog -golden -version sv2012 {
    eth_vlg_pkg.sv
    eth_vlg_tmr.sv
    ipv4_vlg_pkg.sv
    mac_vlg_pkg.sv
    pnrg.sv
    tcp_ctl_ifc.sv
    tcp_ifc.sv
    tcp_rx_ctl_ifc.sv
    tcp_tx_ctl_ifc.sv
    tcp_vlg_engine.sv
    tcp_vlg_fast_rtx.sv
    tcp_vlg_ka.sv
    tcp_vlg_pkg.sv
    tcp_vlg_tx_arb.sv
}

elaborate    -golden
set_mode mv

read_sva {../tcp_server_binding.sv ../tcp_server_pkg.sv ../tcp_server_aip_3.sv}

#check -all [get_assertions]