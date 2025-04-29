####################################################
# Copyright(c) LUBIS EDA GmbH, All rights reserved #
# Contact: contact@lubis-eda.com                   #
####################################################
#--------------------------------------------------------------------
# Setup mode
#--------------------------------------------------------------------
set_mode setup
delete_design -both
#------------------
# Set path variable
#------------------
set SCRIPT_LOCATION [file dirname [file normalize [info script]]]

#------------------
# Read RTL files:
#------------------
read_verilog -golden  -pragma_ignore {}  -version sv2012 {$SCRIPT_LOCATION/VerificationWrapper.sv}

elaborate -golden
compile -golden
#--------------------------------------------------------------------
# MV mode
#--------------------------------------------------------------------
set_mode mv
#set_check_option -verbose
#time {check -all [get_checks]}