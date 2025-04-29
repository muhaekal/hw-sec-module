// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 10.12.2024 at 14:23                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


bind uart_tx fv_uart_tx_m fv_uart_tx(
  .rst(uart_tx.rst),
  .clk(uart_tx.clk),

  // Ports
  .current_cnt(uart_tx.bit_cnt),

  .t_data_port_vld(uart_tx.s_axis_tvalid),
  .t_data_port_rdy(!uart_tx.busy),
  .t_data_port(uart_tx.s_axis_tdata),

  .busy_port(uart_tx.busy),

  .cnt_new(uart_tx.bit_cnt),

  .tready_port(uart_tx.s_axis_tready),

  .txd_port(uart_tx.txd),

  // Registers
  .t_data(uart_tx.data_reg[7:0]),
 // .t_data(uart_tx.s_axis_tdata),

  // States
  .IDLE(!uart_tx.busy),
  .TRANSMIT_DATA((uart_tx.bit_cnt >=  1 && uart_tx.bit_cnt <= 9 & uart_tx.prescale_reg == 7) || (uart_tx.bit_cnt == 0 & uart_tx.busy & uart_tx.prescale_reg == 8))
);
