// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.03.2025 at 11:38                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import global_package::*;
import i2c_controller_operations::*;


module i2c_controller (
  input  logic                 rst,
  input  logic                 clk,
  input  logic unsigned [7:0]  addr,
  output logic unsigned [23:0] data_rcv,
  input  logic unsigned [23:0] data_rcv_in,
  input  logic unsigned [23:0] data_snt,
  output logic unsigned [0:0]  scl,
  input  logic unsigned [0:0]  sda_in,
  output logic unsigned [0:0]  sda_out,
  input  logic unsigned [0:0]  start
);

  logic unsigned [0:0]        ack;
  logic unsigned [3:0]        bit_count_addr;
  logic unsigned [3:0]        bit_count_data;
  logic unsigned [9:0]        count_thd;
  logic unsigned [9:0]        count_thigh;
  logic unsigned [9:0]        count_tlow;
  logic unsigned [1:0]        rcvd_byte;
  logic unsigned [0:0]        rw;
  logic unsigned [1:0]        sent_byte;
  i2c_controller_operations_t operation;

  i2c_controller_control i2c_controller_control_inst (
    .rst           (rst),
    .clk           (clk),
    .start         (start),
    .ack           (ack),
    .bit_count_addr(bit_count_addr),
    .bit_count_data(bit_count_data),
    .count_thd     (count_thd),
    .count_thigh   (count_thigh),
    .count_tlow    (count_tlow),
    .rcvd_byte     (rcvd_byte),
    .rw            (rw),
    .sent_byte     (sent_byte),
    .operation     (operation)
  );

  i2c_controller_computational i2c_controller_computational_inst (
    .rst               (rst),
    .clk               (clk),
    .addr              (addr),
    .data_rcv          (data_rcv),
    .data_rcv_in       (data_rcv_in),
    .data_snt          (data_snt),
    .scl               (scl),
    .sda_in            (sda_in),
    .sda_out           (sda_out),
    .start             (start),
    .ack_out           (ack),
    .bit_count_addr_out(bit_count_addr),
    .bit_count_data_out(bit_count_data),
    .count_thd_out     (count_thd),
    .count_thigh_out   (count_thigh),
    .count_tlow_out    (count_tlow),
    .rcvd_byte_out     (rcvd_byte),
    .rw_out            (rw),
    .sent_byte_out     (sent_byte),
    .operation         (operation)
  );

endmodule
