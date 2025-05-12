`include "master_I2C_copy.sv"
`include "i2c_controller.sv"
`include "i2c_controller_pkg.sv"
`include "i2c_controller_computational.sv"
`include "i2c_controller_control.sv"
`include "i2c_controller_operations.sv"
`include "global_package.sv"

/*module i2c_top (
    input  logic                 clk,
    input  logic                 rst,
    input  logic                 start,
    input  logic [7:0]           addr_target,
    input  logic [23:0]          data_send,
    input  logic [1:0]           num_bytes_send,
    input  logic [1:0]           num_bytes_receive,
    output logic                 match
);*/


module i2c_top #(
    parameter THD_STA=4, parameter TLOW=5, parameter THIGH=4, parameter TSU_DAT=2, parameter TSU_STO=4, parameter THIGH_SAMPLE=1
)(
  input logic clk,
  input logic rst,
  input logic start,
  input logic [7:0] addr_target,
  input logic [23:0] data_send,
  input logic SCL_rx,
  input logic SDA_rx,
  output logic match

);

    // Internal wires
    logic [23:0] data_received_master;
    logic [23:0] data_received_controller;
    logic        scl_master, scl_controller;
    logic        sda_master, sda_controller;

    // Instantiate master_I2C
    master_I2C master_inst (
        .rst               (rst),
        .clk               (clk),
        .start             (start),
        .addr_target       (addr_target),
        .data_send         (data_send),
        .num_bytes_send    (3),
        .num_bytes_receive (3),
        .SDA_tx            (sda_master),
        .SDA_rx            (SDA_rx),
        .SCL_tx            (scl_master),
        .SCL_rx            (SCL_rx),
        .data_received     (data_received_master)
    );

    // Instantiate i2c_controller
    i2c_controller controller_inst (
        .rst         (!rst),
        .clk         (clk),
        .addr        (addr_target),
        .data_rcv    (data_received_controller),
        .data_rcv_in (data_received_controller),
        .data_snt    (data_send),
        .scl         (scl_controller),
        .sda_in      (SDA_rx),
        .sda_out     (sda_controller),
        .start       (start)
    );

    assign match = (data_received_master == data_received_controller) &&
                   (sda_master == sda_controller) &&
                   (scl_master == scl_controller);

endmodule
