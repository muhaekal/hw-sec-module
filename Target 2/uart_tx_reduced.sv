// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 22.12.2024 at 12:38                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


module fv_uart_tx_reduced_m(
  input logic rst,
  input logic clk,

  // Ports
  input logic t_data_port_vld,
  input logic t_data_port_rdy,
  input logic unsigned [7:0] t_data_port,

  input logic unsigned [0:0] txd_port,

  input logic tready_port,

  input logic busy_port,

  // States
  input logic IDLE,
  input logic TRANSMIT_START,
  input logic TRANSMIT_STOP
);


default clocking default_clk @(posedge clk); endclocking


sequence reset_sequence;
  rst ##1 !rst;
endsequence

property set_prescale;
    uart_tx.prescale == 1'b1;
endproperty
assume_set_prescale: assume property (disable iff(rst) set_prescale);

property no_valid_while_busy;
    uart_tx.busy
    |->
    !uart_tx.s_axis_tvalid;
endproperty
assume_no_valid_while_busy: assume property (disable iff(rst) no_valid_while_busy); //to not have a valid signal during busy 
//so that from transmit stop state, it will transition to idle state

property run_reset_p;
  reset_sequence |->
  IDLE &&
  busy_port == 0 &&
  tready_port == 1 &&
  txd_port == 1'd1;
endproperty
run_reset_a: assert property (run_reset_p);


property run_IDLE_to_TRANSMIT_START_p;
  IDLE &&
  t_data_port_vld
|->
  ##1
  TRANSMIT_START &&
  busy_port == 1 &&
  tready_port == 0 &&
  txd_port == 1'd0;
endproperty
run_IDLE_to_TRANSMIT_START_a: assert property (disable iff(rst) run_IDLE_to_TRANSMIT_START_p);


property run_TRANSMIT_START_to_TRANSMIT_STOP_p;
  TRANSMIT_START
|->
  ##1 ($stable(busy_port))[*71] and
  ##1 ($stable(tready_port))[*71] and
  //##1 ($stable(txd_port))[*71] and
  ##72
  TRANSMIT_STOP &&
  busy_port == 1 &&
  tready_port == 0 &&
  txd_port == 1'd1;
endproperty
run_TRANSMIT_START_to_TRANSMIT_STOP_a: assert property (disable iff(rst) run_TRANSMIT_START_to_TRANSMIT_STOP_p);


property run_TRANSMIT_STOP_to_IDLE_p;
  TRANSMIT_STOP
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
run_TRANSMIT_STOP_to_IDLE_a: assert property (disable iff(rst) run_TRANSMIT_STOP_to_IDLE_p);


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

/*
property run_IDLE_eventually_left_p;
  IDLE
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(rst) run_IDLE_eventually_left_p);


property run_TRANSMIT_START_eventually_left_p;
  TRANSMIT_START
|->
  s_eventually(!TRANSMIT_START);
endproperty
run_TRANSMIT_START_eventually_left_a: assert property (disable iff(rst) run_TRANSMIT_START_eventually_left_p);


property run_TRANSMIT_STOP_eventually_left_p;
  TRANSMIT_STOP
|->
  s_eventually(!TRANSMIT_STOP);
endproperty
run_TRANSMIT_STOP_eventually_left_a: assert property (disable iff(rst) run_TRANSMIT_STOP_eventually_left_p);


parameter SANITY = 1;
if (SANITY) begin
// Check that no more than 1 state condition is met at the same time
  run_sanity_onehot0_state: assert property ( $onehot0({IDLE, TRANSMIT_START, TRANSMIT_STOP}) );
end
*/

endmodule
