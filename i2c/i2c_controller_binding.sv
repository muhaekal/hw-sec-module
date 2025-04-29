// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 13.03.2025 at 14:22                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


bind master_I2C fv_i2c_controller_m fv_i2c_controller(
  .rst(!master_I2C.rst),
  .clk(master_I2C.clk),

  // Ports
  .addr(master_I2C.addr_target),

  .data_rcv_in(master_I2C.data_received),

  .data_snt(master_I2C.data_send),

  .sda_in(master_I2C.SDA_rx),

  .start(master_I2C.initial_comm),

  .data_rcv(master_I2C.data_received),

  .scl(master_I2C.SCL_tx),

  .sda_out(master_I2C.SDA_tx),

  // Registers
  .ack(master_I2C.ack),
  .addr_shift_reg(master_I2C.addr_target_sampled),
  .bit_count_addr(master_I2C.count_addr),
  .bit_count_data(master_I2C.count_data),
  .count_thd(master_I2C.count_initiate),
  .count_thigh(master_I2C.count_high),
  .count_tlow(master_I2C.count_low),
  .data_shift_reg(master_I2C.data_send_sampled),
  .rcvd_byte(master_I2C.count_bytes_received),
  .rw(master_I2C.rw),
  .sent_byte(master_I2C.count_bytes_send),

  // States
  .HIGH_ADDR_ACK_S(master_I2C.state == BIT_CYCLE_HIGH_ADDR_ACK),
  .HIGH_CLK_ADDR_S(master_I2C.state == BIT_CYCLE_HIGH_ADDR),
  .HIGH_CLK_DATA_S(master_I2C.state == BIT_CYCLE_HIGH_DATA),
  .HIGH_DATA_ACK_S(master_I2C.state == BIT_CYCLE_HIGH_DATA_ACK),
  .HIGH_STOP_S(master_I2C.state == TERMINATE_HIGH),
  .IDLE_S(master_I2C.state == IDLE),
  .LOW_ADDR_ACK_S(master_I2C.state == BIT_CYCLE_LOW_ADDR_ACK),
  .LOW_CLK_ADDR_S(master_I2C.state == BIT_CYCLE_LOW_ADDR),
  .LOW_CLK_DATA_S(master_I2C.state == BIT_CYCLE_LOW_DATA),
  .LOW_DATA_ACK_S(master_I2C.state == BIT_CYCLE_LOW_DATA_ACK),
  .LOW_STOP_S(master_I2C.state == TERMINATE_LOW),
  .START_S(master_I2C.state == INITIATE)
);
