// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 13.03.2025 at 14:22                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


bind i2c_controller fv_i2c_controller_m fv_i2c_controller(
  .rst(i2c_controller.rst),
  .clk(i2c_controller.clk),

  // Ports
  .addr(i2c_controller.addr),

  .data_rcv_in(i2c_controller.data_rcv_in),

  .data_snt(i2c_controller.data_snt),

  .sda_in(i2c_controller.sda_in),

  .start(i2c_controller.start),

  .data_rcv(i2c_controller.data_rcv),

  .scl(i2c_controller.scl),

  .sda_out(i2c_controller.sda_out),

  // Registers
  .ack(i2c_controller.ack),
  .addr_shift_reg(i2c_controller.i2c_controller_computational_inst.addr_shift_reg),
  .bit_count_addr(i2c_controller.bit_count_addr),
  .bit_count_data(i2c_controller.bit_count_data),
  .count_thd(i2c_controller.count_thd),
  .count_thigh(i2c_controller.count_thigh),
  .count_tlow(i2c_controller.count_tlow),
  .data_shift_reg(i2c_controller.i2c_controller_computational_inst.data_shift_reg),
  .rcvd_byte(i2c_controller.rcvd_byte),
  .rw(i2c_controller.rw),
  .sent_byte(i2c_controller.sent_byte),

  // States
  .HIGH_ADDR_ACK_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_HIGH_ADDR_ACK_S),
  .HIGH_CLK_ADDR_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_HIGH_CLK_ADDR_S),
  .HIGH_CLK_DATA_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_HIGH_CLK_DATA_S),
  .HIGH_DATA_ACK_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_HIGH_DATA_ACK_S),
  .HIGH_STOP_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_HIGH_STOP_S),
  .IDLE_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_IDLE_S),
  .LOW_ADDR_ACK_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_LOW_ADDR_ACK_S),
  .LOW_CLK_ADDR_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_LOW_CLK_ADDR_S),
  .LOW_CLK_DATA_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_LOW_CLK_DATA_S),
  .LOW_DATA_ACK_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_LOW_DATA_ACK_S),
  .LOW_STOP_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_LOW_STOP_S),
  .START_S(i2c_controller.i2c_controller_control_inst.current_state == i2c_controller_START_S)
);
