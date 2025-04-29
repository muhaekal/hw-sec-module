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
    master_I2C.sv
}

elaborate    -golden
set_mode mv

read_sva {i2c_controller_binding.sv i2c_controller_pkg.sv i2c_controller_aip.sv}

#check -all [get_assertions]