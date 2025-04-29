// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 22.12.2024 at 12:03                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


bind uart_tx fv_uart_tx_reduced_m fv_uart_tx_reduced(
  .rst(uart_tx.rst),
  .clk(uart_tx.clk),

  // Ports
  .t_data_port_vld(uart_tx.s_axis_tvalid),
  .t_data_port_rdy(!uart_tx.busy),
  .t_data_port(uart_tx.s_axis_tdata),

  .busy_port(uart_tx.busy),

  .tready_port(uart_tx.s_axis_tready),

  .txd_port(uart_tx.txd),

  // States
  .IDLE(!uart_tx.busy),
  .TRANSMIT_START(uart_tx.bit_cnt == 9 & uart_tx.prescale_reg == 7),
  .TRANSMIT_STOP(uart_tx.bit_cnt == 0 & uart_tx.busy & uart_tx.prescale_reg == 8)
);
