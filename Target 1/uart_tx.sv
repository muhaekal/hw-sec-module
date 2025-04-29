// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 27.01.2025 at 14:12                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


module fv_uart_tx_m(
  input logic rst,
  input logic clk,

  // Ports
  input logic t_data_port_vld,
  input logic t_data_port_rdy,
  input logic unsigned [7:0] t_data_port,

  input logic unsigned [3:0] current_cnt,

  input logic unsigned [3:0] cnt_new,

  input logic unsigned [0:0] txd_port,

  input logic tready_port,

  input logic busy_port,

  // Registers
  input logic unsigned [7:0] t_data,

  // States
  input logic IDLE,
  input logic TRANSMIT_DATA
);


default clocking default_clk @(posedge clk); endclocking


sequence reset_sequence;
  rst ##1 !rst;
endsequence


property run_reset_p;
  reset_sequence |->
  IDLE &&
  busy_port == 0 &&
  tready_port == 1 &&
  txd_port == 1'd1;
endproperty
run_reset_a: assert property (run_reset_p);


property run_IDLE_to_TRANSMIT_DATA_p;
  IDLE &&
  t_data_port_vld
|->
  ##1
  TRANSMIT_DATA &&
  busy_port == 1 &&
  tready_port == 0 &&
  txd_port == 1'd0;
endproperty
run_IDLE_to_TRANSMIT_DATA_a: assert property (disable iff(rst) run_IDLE_to_TRANSMIT_DATA_p);


property run_TRANSMIT_DATA_to_IDLE_p;
  TRANSMIT_DATA &&
  (current_cnt <= 64'd0)
|->
  ##1 ($stable(busy_port))[*8] and
  ##1 ($stable(tready_port))[*8] and
  ##1 ($stable(txd_port))[*8] and
  ##9
  IDLE &&
  busy_port == 0 &&
  tready_port == 1 &&
  txd_port == 1'd1;
endproperty
run_TRANSMIT_DATA_to_IDLE_a: assert property (disable iff(rst) run_TRANSMIT_DATA_to_IDLE_p);


property run_TRANSMIT_DATA_to_TRANSMIT_DATA_p;
  TRANSMIT_DATA &&
  (current_cnt > 64'd0)
|->
  ##1 ($stable(busy_port))[*7] and
  ##1 ($stable(tready_port))[*8] and
  ##1 ($stable(txd_port))[*7] and
  ##8
  TRANSMIT_DATA &&
  busy_port == 1 &&
  txd_port == { $past(t_data, 8) }[0];
endproperty
run_TRANSMIT_DATA_to_TRANSMIT_DATA_a: assert property (disable iff(rst) run_TRANSMIT_DATA_to_TRANSMIT_DATA_p);


property run_IDLE_wait_p;
  IDLE &&
  !t_data_port_vld
|->
  ##1 ($stable(busy_port)) and
  ##1 ($stable(tready_port)) and
  ##1 ($stable(txd_port)) and
  ##1
  IDLE;
endproperty
run_IDLE_wait_a: assert property (disable iff(rst) run_IDLE_wait_p);


property run_IDLE_eventually_left_p;
  IDLE
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(rst) run_IDLE_eventually_left_p);


property run_TRANSMIT_DATA_eventually_left_p;
  TRANSMIT_DATA
|->
  s_eventually(!TRANSMIT_DATA);
endproperty
run_TRANSMIT_DATA_eventually_left_a: assert property (disable iff(rst) run_TRANSMIT_DATA_eventually_left_p);


parameter SANITY = 1;
if (SANITY) begin
// Check that no more than 1 state condition is met at the same time
  run_sanity_onehot0_state: assert property ( $onehot0({IDLE, TRANSMIT_DATA}) );
end


endmodule
