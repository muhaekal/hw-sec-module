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
    global_package.sv
    tcp_server_operations.sv
    tcp_server_control.sv
    tcp_server_computational.sv
    tcp_server.sv
}

elaborate    -golden
set_mode mv

read_sva {../tcp_server_binding_ols.sv ../tcp_server_pkg.sv ../tcp_server_aip_ols.sv}

#check -all [get_assertions]