`include "master_I2C_copy.sv"
`include "i2c_controller.sv"
`include "i2c_controller_pkg.sv"
`include "i2c_controller_computational.sv"
`include "i2c_controller_control.sv"
`include "i2c_controller_operations.sv"
`include "global_package.sv"


module VerificationWrapper #(
    parameter THD_STA=4, parameter TLOW=5, parameter THIGH=4, parameter TSU_DAT=2, parameter TSU_STO=4, parameter THIGH_SAMPLE=1
)(
  input logic clk,
  input logic rst,
  input logic start,
  input logic [7:0] addr_target,
  input logic [23:0] data_send,
  output logic [23:0] data_received,
  output logic SCL_tx,
  input logic SCL_rx,
  output logic SDA_tx,
  input logic SDA_rx

);

//DUT instantiation
master_I2C dut_inst (
  .clk(clk),
  .rst(rst),
  .start(start),
  .addr_target(addr_target),
  .data_send(data_send),
  .num_bytes_send(3),
  .num_bytes_receive(3),
  .SDA_tx(SDA_tx),
  .SCL_tx(SCL_tx),
  .SDA_rx(SDA_rx),
  .SCL_rx(SCL_rx),
  .data_received(data_received)
);


//Generated RTL instantiation
i2c_controller i2c_controller (
  .rst(!rst),
  .clk(clk),
  .addr(addr_target),
  .data_rcv(),
  .data_rcv_in(data_received),
  .data_snt(data_send),
  .scl(),
  .sda_in(SDA_rx),
  .sda_out(),
  .start(start)
);


default clocking default_clk @(posedge clk); endclocking

property SDA_constraints_p;
   (i2c_controller.sda_out == 1'd1)
|->
    SDA_rx == 1'd1 ||
    SDA_rx == 1'd0;
endproperty
SDA_constraints_a: assume property (disable iff(!rst) SDA_constraints_p);


property stable_addr_p;
   $stable(i2c_controller.addr) &&
   $stable(i2c_controller.data_snt);
endproperty
stable_addr_a: assume property (disable iff(!rst) stable_addr_p);

sequence reset_sequence;
  !rst ##1 rst;
endsequence

sequence reset_p_sequence;
  reset_sequence;
endsequence

property reset_p_ec;
  reset_p_sequence
  |->
  i2c_controller.scl == SCL_tx;
endproperty
reset_a_ec: assert property (reset_p_ec);

property reset_1_p_ec;
  reset_p_sequence
  |->
  i2c_controller.sda_out == SDA_tx;
endproperty
reset_1_a_ec: assert property (reset_1_p_ec);

property reset_2_p_ec;
  reset_p_sequence
  |->
  i2c_controller.data_rcv == data_received;
endproperty
reset_2_a_ec: assert property (reset_2_p_ec);

sequence idle_to_idle_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 0) &&
  (i2c_controller.start == 1'd0);
endsequence

property idle_to_idle_p_ec;
  idle_to_idle_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
idle_to_idle_a_ec: assert property (disable iff(!rst) idle_to_idle_p_ec);

property idle_to_idle_1p_ec;
  idle_to_idle_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
idle_to_idle_1a_ec: assert property (disable iff(!rst) idle_to_idle_1p_ec);

property idle_to_idle_2p_ec;
  idle_to_idle_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
idle_to_idle_2a_ec: assert property (disable iff(!rst) idle_to_idle_2p_ec);

sequence idle_to_start_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 0) &&
  (i2c_controller.start != 1'd0);
endsequence

property idle_to_start_p_ec;
  idle_to_start_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
idle_to_start_a_ec: assert property (disable iff(!rst) idle_to_start_p_ec);

property idle_to_start_1p_ec;
  idle_to_start_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
idle_to_start_1a_ec: assert property (disable iff(!rst) idle_to_start_1p_ec);

property idle_to_start_2p_ec;
  idle_to_start_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
idle_to_start_2a_ec: assert property (disable iff(!rst) idle_to_start_2p_ec);

sequence start_to_start_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 1) &&
  (i2c_controller.count_thd < THD_STA);
endsequence

property start_to_start_p_ec; 
  start_to_start_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
start_to_start_a_ec: assert property (disable iff(!rst) start_to_start_p_ec);

property start_to_start_1p_ec; 
  start_to_start_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
start_to_start_1a_ec: assert property (disable iff(!rst) start_to_start_1p_ec);

property start_to_start_2p_ec; 
  start_to_start_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
start_to_start_2a_ec: assert property (disable iff(!rst) start_to_start_2p_ec);

sequence start_to_low_clk_addr_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 1) &&
  (i2c_controller.count_thd >= THD_STA);
endsequence

property start_to_low_clk_addr_p_ec;
  start_to_low_clk_addr_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
start_to_low_clk_addr_a_ec: assert property (disable iff(!rst) start_to_low_clk_addr_p_ec);

property start_to_low_clk_addr_1p_ec;
  start_to_low_clk_addr_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
start_to_low_clk_addr_1a_ec: assert property (disable iff(!rst) start_to_low_clk_addr_1p_ec);

property start_to_low_clk_addr_2p_ec;
  start_to_low_clk_addr_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
start_to_low_clk_addr_2a_ec: assert property (disable iff(!rst) start_to_low_clk_addr_2p_ec);

sequence low_clk_addr_to_low_clk_addr_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 2) &&
  (i2c_controller.count_tlow == (TLOW-TSU_DAT));
endsequence

property low_clk_addr_to_low_clk_addr_p_ec;
  low_clk_addr_to_low_clk_addr_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_clk_addr_to_low_clk_addr_a_ec: assert property (disable iff(!rst) low_clk_addr_to_low_clk_addr_p_ec);

property low_clk_addr_to_low_clk_addr_1p_ec;
  low_clk_addr_to_low_clk_addr_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_clk_addr_to_low_clk_addr_1a_ec: assert property (disable iff(!rst) low_clk_addr_to_low_clk_addr_1p_ec);

property low_clk_addr_to_low_clk_addr_2p_ec;
  low_clk_addr_to_low_clk_addr_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_clk_addr_to_low_clk_addr_2a_ec: assert property (disable iff(!rst) low_clk_addr_to_low_clk_addr_2p_ec);


sequence low_clk_addr_to_low_clk_addr_1_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 2) &&
  (i2c_controller.count_tlow != (TLOW-TSU_DAT)) &&
  (i2c_controller.count_tlow < TLOW);
endsequence

property low_clk_addr_to_low_clk_addr_1_p_ec;
  low_clk_addr_to_low_clk_addr_1_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_clk_addr_to_low_clk_addr_1_a_ec: assert property (disable iff(!rst) low_clk_addr_to_low_clk_addr_1_p_ec);

property low_clk_addr_to_low_clk_addr_1_1p_ec;
  low_clk_addr_to_low_clk_addr_1_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_clk_addr_to_low_clk_addr_1_1a_ec: assert property (disable iff(!rst) low_clk_addr_to_low_clk_addr_1_1p_ec);

property low_clk_addr_to_low_clk_addr_1_2p_ec;
  low_clk_addr_to_low_clk_addr_1_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_clk_addr_to_low_clk_addr_1_2a_ec: assert property (disable iff(!rst) low_clk_addr_to_low_clk_addr_1_2p_ec);

sequence low_clk_addr_to_high_clk_addr_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 2) &&
  (i2c_controller.count_tlow >= TLOW);
endsequence

property low_clk_addr_to_high_clk_addr_p_ec;
  low_clk_addr_to_high_clk_addr_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_clk_addr_to_high_clk_addr_a_ec: assert property (disable iff(!rst) low_clk_addr_to_high_clk_addr_p_ec);

property low_clk_addr_to_high_clk_addr_1p_ec;
  low_clk_addr_to_high_clk_addr_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_clk_addr_to_high_clk_addr_1a_ec: assert property (disable iff(!rst) low_clk_addr_to_high_clk_addr_1p_ec);

property low_clk_addr_to_high_clk_addr_2p_ec;
  low_clk_addr_to_high_clk_addr_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_clk_addr_to_high_clk_addr_2a_ec: assert property (disable iff(!rst) low_clk_addr_to_high_clk_addr_2p_ec);


sequence high_clk_addr_to_high_clk_addr_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 3) &&
  (i2c_controller.count_thigh < THIGH);
endsequence

property high_clk_addr_to_high_clk_addr_p_ec;
  high_clk_addr_to_high_clk_addr_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_clk_addr_to_high_clk_addr_a_ec: assert property (disable iff(!rst) high_clk_addr_to_high_clk_addr_p_ec);

property high_clk_addr_to_high_clk_addr_1p_ec;
  high_clk_addr_to_high_clk_addr_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_clk_addr_to_high_clk_addr_1a_ec: assert property (disable iff(!rst) high_clk_addr_to_high_clk_addr_1p_ec);

property high_clk_addr_to_high_clk_addr_2p_ec;
  high_clk_addr_to_high_clk_addr_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_clk_addr_to_high_clk_addr_2a_ec: assert property (disable iff(!rst) high_clk_addr_to_high_clk_addr_2p_ec);


sequence high_clk_addr_to_low_clk_addr_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 3) &&
  (i2c_controller.count_thigh >= THIGH) &&
  (i2c_controller.bit_count_addr < 8);
endsequence

property high_clk_addr_to_low_clk_addr_p_ec;
  high_clk_addr_to_low_clk_addr_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_clk_addr_to_low_clk_addr_a_ec: assert property (disable iff(!rst) high_clk_addr_to_low_clk_addr_p_ec);

property high_clk_addr_to_low_clk_addr_1p_ec;
  high_clk_addr_to_low_clk_addr_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_clk_addr_to_low_clk_addr_1a_ec: assert property (disable iff(!rst) high_clk_addr_to_low_clk_addr_1p_ec);

property high_clk_addr_to_low_clk_addr_2p_ec;
  high_clk_addr_to_low_clk_addr_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_clk_addr_to_low_clk_addr_2a_ec: assert property (disable iff(!rst) high_clk_addr_to_low_clk_addr_2p_ec);


sequence high_clk_addr_to_low_addr_ack_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 3) &&
  (i2c_controller.count_thigh >= THIGH) &&
  (i2c_controller.bit_count_addr >= 8);
endsequence

property high_clk_addr_to_low_addr_ack_p_ec;
  high_clk_addr_to_low_addr_ack_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_clk_addr_to_low_addr_ack_a_ec: assert property (disable iff(!rst) high_clk_addr_to_low_addr_ack_p_ec);

property high_clk_addr_to_low_addr_ack_1p_ec;
  high_clk_addr_to_low_addr_ack_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_clk_addr_to_low_addr_ack_1a_ec: assert property (disable iff(!rst) high_clk_addr_to_low_addr_ack_1p_ec);

property high_clk_addr_to_low_addr_ack_2p_ec;
  high_clk_addr_to_low_addr_ack_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_clk_addr_to_low_addr_ack_2a_ec: assert property (disable iff(!rst) high_clk_addr_to_low_addr_ack_2p_ec);


sequence low_addr_ack_to_low_addr_ack_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 4) &&
  (i2c_controller.count_tlow < TLOW);
endsequence

property low_addr_ack_to_low_addr_ack_p_ec;
  low_addr_ack_to_low_addr_ack_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_addr_ack_to_low_addr_ack_a_ec: assert property (disable iff(!rst) low_addr_ack_to_low_addr_ack_p_ec);

property low_addr_ack_to_low_addr_ack_1p_ec;
  low_addr_ack_to_low_addr_ack_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_addr_ack_to_low_addr_ack_1a_ec: assert property (disable iff(!rst) low_addr_ack_to_low_addr_ack_1p_ec);

property low_addr_ack_to_low_addr_ack_2p_ec;
  low_addr_ack_to_low_addr_ack_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_addr_ack_to_low_addr_ack_2a_ec: assert property (disable iff(!rst) low_addr_ack_to_low_addr_ack_2p_ec);


sequence low_addr_ack_to_high_addr_ack_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 4) &&
  (i2c_controller.count_tlow >= TLOW);
endsequence

property low_addr_ack_to_high_addr_ack_p_ec;
  low_addr_ack_to_high_addr_ack_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_addr_ack_to_high_addr_ack_a_ec: assert property (disable iff(!rst) low_addr_ack_to_high_addr_ack_p_ec);

property low_addr_ack_to_high_addr_ack_1p_ec;
  low_addr_ack_to_high_addr_ack_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_addr_ack_to_high_addr_ack_1a_ec: assert property (disable iff(!rst) low_addr_ack_to_high_addr_ack_1p_ec);

property low_addr_ack_to_high_addr_ack_2p_ec;
  low_addr_ack_to_high_addr_ack_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_addr_ack_to_high_addr_ack_2a_ec: assert property (disable iff(!rst) low_addr_ack_to_high_addr_ack_2p_ec);


sequence high_addr_ack_to_high_addr_ack_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 5) &&
  (i2c_controller.count_thigh == THIGH_SAMPLE);
endsequence

property high_addr_ack_to_high_addr_ack_p_ec;
  high_addr_ack_to_high_addr_ack_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_addr_ack_to_high_addr_ack_a_ec: assert property (disable iff(!rst) high_addr_ack_to_high_addr_ack_p_ec);

property high_addr_ack_to_high_addr_ack_1p_ec;
  high_addr_ack_to_high_addr_ack_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_addr_ack_to_high_addr_ack_1a_ec: assert property (disable iff(!rst) high_addr_ack_to_high_addr_ack_1p_ec);

property high_addr_ack_to_high_addr_ack_2p_ec;
  high_addr_ack_to_high_addr_ack_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_addr_ack_to_high_addr_ack_2a_ec: assert property (disable iff(!rst) high_addr_ack_to_high_addr_ack_2p_ec);


sequence high_addr_ack_to_high_addr_ack_1_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 5) &&
  (i2c_controller.count_thigh != THIGH_SAMPLE) &&
  (i2c_controller.count_thigh < THIGH);
endsequence

property high_addr_ack_to_high_addr_ack_1_p_ec;
  high_addr_ack_to_high_addr_ack_1_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_addr_ack_to_high_addr_ack_1_a_ec: assert property (disable iff(!rst) high_addr_ack_to_high_addr_ack_1_p_ec);

property high_addr_ack_to_high_addr_ack_1_1p_ec;
  high_addr_ack_to_high_addr_ack_1_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_addr_ack_to_high_addr_ack_1_1a_ec: assert property (disable iff(!rst) high_addr_ack_to_high_addr_ack_1_1p_ec);

property high_addr_ack_to_high_addr_ack_1_2p_ec;
  high_addr_ack_to_high_addr_ack_1_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_addr_ack_to_high_addr_ack_1_2a_ec: assert property (disable iff(!rst) high_addr_ack_to_high_addr_ack_1_2p_ec);

sequence high_addr_ack_to_low_clk_data_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 5) &&
  (i2c_controller.count_thigh >= THIGH);
endsequence

property high_addr_ack_to_low_clk_data_p_ec;
  high_addr_ack_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_addr_ack_to_low_clk_data_a_ec: assert property (disable iff(!rst) high_addr_ack_to_low_clk_data_p_ec);

property high_addr_ack_to_low_clk_data_1p_ec;
  high_addr_ack_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_addr_ack_to_low_clk_data_1a_ec: assert property (disable iff(!rst) high_addr_ack_to_low_clk_data_1p_ec);

property high_addr_ack_to_low_clk_data_2p_ec;
  high_addr_ack_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_addr_ack_to_low_clk_data_2a_ec: assert property (disable iff(!rst) high_addr_ack_to_low_clk_data_2p_ec);


sequence low_clk_data_to_low_clk_data_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 6) &&
  (i2c_controller.ack == 0) &&
  (i2c_controller.count_tlow == (TLOW-TSU_DAT)) &&
  (i2c_controller.rw == 0);
endsequence

property low_clk_data_to_low_clk_data_p_ec;
  low_clk_data_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_clk_data_to_low_clk_data_a_ec: assert property (disable iff(!rst) low_clk_data_to_low_clk_data_p_ec);

property low_clk_data_to_low_clk_data_1p_ec;
  low_clk_data_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_clk_data_to_low_clk_data_1a_ec: assert property (disable iff(!rst) low_clk_data_to_low_clk_data_1p_ec);

property low_clk_data_to_low_clk_data_2p_ec;
  low_clk_data_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_clk_data_to_low_clk_data_2a_ec: assert property (disable iff(!rst) low_clk_data_to_low_clk_data_2p_ec);


sequence low_clk_data_to_low_clk_data_1_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 6) &&
  (i2c_controller.ack == 0) &&
  (i2c_controller.count_tlow < TLOW) &&
  (i2c_controller.rw == 1);
endsequence

property low_clk_data_to_low_clk_data_1_p_ec;
  low_clk_data_to_low_clk_data_1_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_clk_data_to_low_clk_data_1_a_ec: assert property (disable iff(!rst) low_clk_data_to_low_clk_data_1_p_ec);

property low_clk_data_to_low_clk_data_1_1p_ec;
  low_clk_data_to_low_clk_data_1_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_clk_data_to_low_clk_data_1_1a_ec: assert property (disable iff(!rst) low_clk_data_to_low_clk_data_1_1p_ec);

property low_clk_data_to_low_clk_data_1_2p_ec;
  low_clk_data_to_low_clk_data_1_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_clk_data_to_low_clk_data_1_2a_ec: assert property (disable iff(!rst) low_clk_data_to_low_clk_data_1_2p_ec);


sequence low_clk_data_to_low_clk_data_2_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 6) &&
  (i2c_controller.ack == 0) &&
  (i2c_controller.count_tlow < TLOW) &&
  (i2c_controller.rw != 1);
endsequence

property low_clk_data_to_low_clk_data_2_p_ec;
  low_clk_data_to_low_clk_data_2_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_clk_data_to_low_clk_data_2_a_ec: assert property (disable iff(!rst) low_clk_data_to_low_clk_data_2_p_ec);

property low_clk_data_to_low_clk_data_2_1p_ec;
  low_clk_data_to_low_clk_data_2_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_clk_data_to_low_clk_data_2_1a_ec: assert property (disable iff(!rst) low_clk_data_to_low_clk_data_2_1p_ec);

property low_clk_data_to_low_clk_data_2_2p_ec;
  low_clk_data_to_low_clk_data_2_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_clk_data_to_low_clk_data_2_2a_ec: assert property (disable iff(!rst) low_clk_data_to_low_clk_data_2_2p_ec);


sequence low_clk_data_to_high_clk_data_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 6) &&
  (i2c_controller.ack == 0) &&
  (i2c_controller.count_tlow >= TLOW);
endsequence

property low_clk_data_to_high_clk_data_p_ec;
  low_clk_data_to_high_clk_data_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_clk_data_to_high_clk_data_a_ec: assert property (disable iff(!rst) low_clk_data_to_high_clk_data_p_ec);

property low_clk_data_to_high_clk_data_1p_ec;
  low_clk_data_to_high_clk_data_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_clk_data_to_high_clk_data_1a_ec: assert property (disable iff(!rst) low_clk_data_to_high_clk_data_1p_ec);

property low_clk_data_to_high_clk_data_2p_ec;
  low_clk_data_to_high_clk_data_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_clk_data_to_high_clk_data_2a_ec: assert property (disable iff(!rst) low_clk_data_to_high_clk_data_2p_ec);


sequence low_clk_data_to_low_stop_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 6) &&
  (i2c_controller.ack != 0);
endsequence

property low_clk_data_to_low_stop_p_ec;
  low_clk_data_to_low_stop_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_clk_data_to_low_stop_a_ec: assert property (disable iff(!rst) low_clk_data_to_low_stop_p_ec);

property low_clk_data_to_low_stop_1p_ec;
  low_clk_data_to_low_stop_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_clk_data_to_low_stop_1a_ec: assert property (disable iff(!rst) low_clk_data_to_low_stop_1p_ec);

property low_clk_data_to_low_stop_2p_ec;
  low_clk_data_to_low_stop_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_clk_data_to_low_stop_2a_ec: assert property (disable iff(!rst) low_clk_data_to_low_stop_2p_ec);


sequence high_clk_data_to_high_clk_data_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 7) &&
  (i2c_controller.count_thigh == THIGH_SAMPLE) &&
  (i2c_controller.rw != 0);
endsequence

property high_clk_data_to_high_clk_data_p_ec;
  high_clk_data_to_high_clk_data_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_clk_data_to_high_clk_data_a_ec: assert property (disable iff(!rst) high_clk_data_to_high_clk_data_p_ec);

property high_clk_data_to_high_clk_data_1p_ec;
  high_clk_data_to_high_clk_data_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_clk_data_to_high_clk_data_1a_ec: assert property (disable iff(!rst) high_clk_data_to_high_clk_data_1p_ec);

property high_clk_data_to_high_clk_data_2p_ec;
  high_clk_data_to_high_clk_data_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_clk_data_to_high_clk_data_2a_ec: assert property (disable iff(!rst) high_clk_data_to_high_clk_data_2p_ec);


sequence high_clk_data_to_high_clk_data_1_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 7) &&
  (i2c_controller.count_thigh != THIGH_SAMPLE) &&
  (i2c_controller.count_thigh < THIGH) &&
  (i2c_controller.rw != 0);
endsequence

property high_clk_data_to_high_clk_data_1_p_ec;
  high_clk_data_to_high_clk_data_1_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_clk_data_to_high_clk_data_1_a_ec: assert property (disable iff(!rst) high_clk_data_to_high_clk_data_1_p_ec);

property high_clk_data_to_high_clk_data_1_1p_ec;
  high_clk_data_to_high_clk_data_1_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_clk_data_to_high_clk_data_1_1a_ec: assert property (disable iff(!rst) high_clk_data_to_high_clk_data_1_1p_ec);

property high_clk_data_to_high_clk_data_1_2p_ec;
  high_clk_data_to_high_clk_data_1_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_clk_data_to_high_clk_data_1_2a_ec: assert property (disable iff(!rst) high_clk_data_to_high_clk_data_1_2p_ec);


sequence high_clk_data_to_low_clk_data_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 7) &&
  (i2c_controller.count_thigh >= THIGH) &&
  (i2c_controller.bit_count_data < 8);
endsequence

property high_clk_data_to_low_clk_data_p_ec;
  high_clk_data_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_clk_data_to_low_clk_data_a_ec: assert property (disable iff(!rst) high_clk_data_to_low_clk_data_p_ec);

property high_clk_data_to_low_clk_data_1p_ec;
  high_clk_data_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_clk_data_to_low_clk_data_1a_ec: assert property (disable iff(!rst) high_clk_data_to_low_clk_data_1p_ec);

property high_clk_data_to_low_clk_data_2p_ec;
  high_clk_data_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_clk_data_to_low_clk_data_2a_ec: assert property (disable iff(!rst) high_clk_data_to_low_clk_data_2p_ec);


sequence high_clk_data_to_low_data_ack_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 7) &&
  (i2c_controller.count_thigh >= THIGH) &&
  (i2c_controller.bit_count_data >= 8);
endsequence

property high_clk_data_to_low_data_ack_p_ec;
  high_clk_data_to_low_data_ack_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_clk_data_to_low_data_ack_a_ec: assert property (disable iff(!rst) high_clk_data_to_low_data_ack_p_ec);

property high_clk_data_to_low_data_ack_1p_ec;
  high_clk_data_to_low_data_ack_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_clk_data_to_low_data_ack_1a_ec: assert property (disable iff(!rst) high_clk_data_to_low_data_ack_1p_ec);

property high_clk_data_to_low_data_ack_2p_ec;
  high_clk_data_to_low_data_ack_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_clk_data_to_low_data_ack_2a_ec: assert property (disable iff(!rst) high_clk_data_to_low_data_ack_2p_ec);


sequence low_data_ack_to_low_data_ack_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 8) &&
  (i2c_controller.count_tlow == (TLOW-TSU_DAT)) &&
  (i2c_controller.rw == 1) &&
  (i2c_controller.rcvd_byte != 2'h2);
endsequence

property low_data_ack_to_low_data_ack_p_ec;
  low_data_ack_to_low_data_ack_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_data_ack_to_low_data_ack_a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_p_ec);

property low_data_ack_to_low_data_ack_1p_ec;
  low_data_ack_to_low_data_ack_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_data_ack_to_low_data_ack_1a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_1p_ec);

property low_data_ack_to_low_data_ack_2p_ec;
  low_data_ack_to_low_data_ack_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_data_ack_to_low_data_ack_2a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_2p_ec);

sequence low_data_ack_to_low_data_ack_1_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 8) &&
  (i2c_controller.count_tlow == (TLOW-TSU_DAT)) &&
  (i2c_controller.rw == 1) &&
  (i2c_controller.rcvd_byte == 2'h2);
endsequence

property low_data_ack_to_low_data_ack_1_p_ec;
  low_data_ack_to_low_data_ack_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_data_ack_to_low_data_ack_1_a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_1_p_ec);

property low_data_ack_to_low_data_ack_1_1p_ec;
  low_data_ack_to_low_data_ack_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_data_ack_to_low_data_ack_1_1a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_1_1p_ec);

property low_data_ack_to_low_data_ack_1_2p_ec;
  low_data_ack_to_low_data_ack_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_data_ack_to_low_data_ack_1_2a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_1_2p_ec);

sequence low_data_ack_to_low_data_ack_2_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 8) &&
  (i2c_controller.count_tlow < TLOW) &&
  (i2c_controller.rw == 0);
endsequence

property low_data_ack_to_low_data_ack_2_p_ec;
  low_data_ack_to_low_data_ack_2_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_data_ack_to_low_data_ack_2_a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_2_p_ec);

property low_data_ack_to_low_data_ack_2_1p_ec;
  low_data_ack_to_low_data_ack_2_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_data_ack_to_low_data_ack_2_1a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_2_1p_ec);

property low_data_ack_to_low_data_ack_2_2p_ec;
  low_data_ack_to_low_data_ack_2_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_data_ack_to_low_data_ack_2_2a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_2_2p_ec);


sequence low_data_ack_to_low_data_ack_3_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 8) &&
  (i2c_controller.count_tlow != (TLOW-TSU_DAT)) &&
  (i2c_controller.count_tlow < TLOW) &&
  (i2c_controller.rw != 0);
endsequence

property low_data_ack_to_low_data_ack_3_p_ec;
  low_data_ack_to_low_data_ack_3_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_data_ack_to_low_data_ack_3_a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_3_p_ec);

property low_data_ack_to_low_data_ack_3_1p_ec;
  low_data_ack_to_low_data_ack_3_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_data_ack_to_low_data_ack_3_1a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_3_1p_ec);

property low_data_ack_to_low_data_ack_3_2p_ec;
  low_data_ack_to_low_data_ack_3_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_data_ack_to_low_data_ack_3_2a_ec: assert property (disable iff(!rst) low_data_ack_to_low_data_ack_3_2p_ec);


sequence low_data_ack_to_high_data_ack_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 8) &&
  (i2c_controller.count_tlow >= TLOW);
endsequence

property low_data_ack_to_high_data_ack_p_ec;
  low_data_ack_to_high_data_ack_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_data_ack_to_high_data_ack_a_ec: assert property (disable iff(!rst) low_data_ack_to_high_data_ack_p_ec);

property low_data_ack_to_high_data_ack_1p_ec;
  low_data_ack_to_high_data_ack_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_data_ack_to_high_data_ack_1a_ec: assert property (disable iff(!rst) low_data_ack_to_high_data_ack_1p_ec);

property low_data_ack_to_high_data_ack_2p_ec;
  low_data_ack_to_high_data_ack_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_data_ack_to_high_data_ack_2a_ec: assert property (disable iff(!rst) low_data_ack_to_high_data_ack_2p_ec);


sequence high_data_ack_to_high_data_ack_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 9) &&
  (i2c_controller.count_thigh == THIGH_SAMPLE) &&
  (i2c_controller.rw == 0);
endsequence

property high_data_ack_to_high_data_ack_p_ec;
  high_data_ack_to_high_data_ack_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_data_ack_to_high_data_ack_a_ec: assert property (disable iff(!rst) high_data_ack_to_high_data_ack_p_ec);

property high_data_ack_to_high_data_ack_1p_ec;
  high_data_ack_to_high_data_ack_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_data_ack_to_high_data_ack_1a_ec: assert property (disable iff(!rst) high_data_ack_to_high_data_ack_1p_ec);

property high_data_ack_to_high_data_ack_2p_ec;
  high_data_ack_to_high_data_ack_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_data_ack_to_high_data_ack_2a_ec: assert property (disable iff(!rst) high_data_ack_to_high_data_ack_2p_ec);

sequence high_data_ack_to_high_data_ack_1_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 9) &&
  (i2c_controller.count_thigh < THIGH) &&
  !((i2c_controller.count_thigh == THIGH_SAMPLE) && (i2c_controller.rw == 0));
endsequence

property high_data_ack_to_high_data_ack_1_p_ec;
  high_data_ack_to_high_data_ack_1_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_data_ack_to_high_data_ack_1_a_ec: assert property (disable iff(!rst) high_data_ack_to_high_data_ack_1_p_ec);

property high_data_ack_to_high_data_ack_1_1p_ec;
  high_data_ack_to_high_data_ack_1_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_data_ack_to_high_data_ack_1_1a_ec: assert property (disable iff(!rst) high_data_ack_to_high_data_ack_1_1p_ec);

property high_data_ack_to_high_data_ack_1_2p_ec;
  high_data_ack_to_high_data_ack_1_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_data_ack_to_high_data_ack_1_2a_ec: assert property (disable iff(!rst) high_data_ack_to_high_data_ack_1_2p_ec);


sequence high_data_ack_to_low_clk_data_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 9) &&
  (i2c_controller.count_thigh >= THIGH) &&
  !((i2c_controller.sent_byte == 2'd3) && (i2c_controller.rw == 0)) &&
  !((i2c_controller.rcvd_byte == 2'd3) && (i2c_controller.rw == 1));
endsequence

property high_data_ack_to_low_clk_data_p_ec;
  high_data_ack_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_data_ack_to_low_clk_data_a_ec: assert property (disable iff(!rst) high_data_ack_to_low_clk_data_p_ec);

property high_data_ack_to_low_clk_data_1p_ec;
  high_data_ack_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_data_ack_to_low_clk_data_1a_ec: assert property (disable iff(!rst) high_data_ack_to_low_clk_data_1p_ec);

property high_data_ack_to_low_clk_data_2p_ec;
  high_data_ack_to_low_clk_data_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_data_ack_to_low_clk_data_2a_ec: assert property (disable iff(!rst) high_data_ack_to_low_clk_data_2p_ec);


sequence high_data_ack_to_low_stop_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 9) &&
  (i2c_controller.count_thigh >= THIGH) &&
  (((i2c_controller.sent_byte == 2'd3) && (i2c_controller.rw == 0)) ||
  ((i2c_controller.rcvd_byte == 2'd3) && (i2c_controller.rw == 1)));
endsequence

property high_data_ack_to_low_stop_p_ec;
  high_data_ack_to_low_stop_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_data_ack_to_low_stop_a_ec: assert property (disable iff(!rst) high_data_ack_to_low_stop_p_ec);

property high_data_ack_to_low_stop_1p_ec;
  high_data_ack_to_low_stop_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_data_ack_to_low_stop_1a_ec: assert property (disable iff(!rst) high_data_ack_to_low_stop_1p_ec);

property high_data_ack_to_low_stop_2p_ec;
  high_data_ack_to_low_stop_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_data_ack_to_low_stop_2a_ec: assert property (disable iff(!rst) high_data_ack_to_low_stop_2p_ec);


sequence low_stop_to_low_stop_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 10) &&
  (i2c_controller.count_tlow == (TLOW-TSU_DAT));
endsequence

property low_stop_to_low_stop_p_ec;
  low_stop_to_low_stop_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_stop_to_low_stop_a_ec: assert property (disable iff(!rst) low_stop_to_low_stop_p_ec);

property low_stop_to_low_stop_1p_ec;
  low_stop_to_low_stop_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_stop_to_low_stop_1a_ec: assert property (disable iff(!rst) low_stop_to_low_stop_1p_ec);

property low_stop_to_low_stop_2p_ec;
  low_stop_to_low_stop_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_stop_to_low_stop_2a_ec: assert property (disable iff(!rst) low_stop_to_low_stop_2p_ec);


sequence low_stop_to_low_stop_1_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 10) &&
  (i2c_controller.count_tlow != (TLOW-TSU_DAT)) &&
  (i2c_controller.count_tlow < TLOW);
endsequence

property low_stop_to_low_stop_1_p_ec;
  low_stop_to_low_stop_1_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_stop_to_low_stop_1_a_ec: assert property (disable iff(!rst) low_stop_to_low_stop_1_p_ec);

property low_stop_to_low_stop_1_1p_ec;
  low_stop_to_low_stop_1_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_stop_to_low_stop_1_1a_ec: assert property (disable iff(!rst) low_stop_to_low_stop_1_1p_ec);

property low_stop_to_low_stop_1_2p_ec;
  low_stop_to_low_stop_1_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_stop_to_low_stop_1_2a_ec: assert property (disable iff(!rst) low_stop_to_low_stop_1_2p_ec);


sequence low_stop_to_high_stop_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 10) &&
  (i2c_controller.count_tlow >= TLOW);
endsequence

property low_stop_to_high_stop_p_ec;
  low_stop_to_high_stop_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
low_stop_to_high_stop_a_ec: assert property (disable iff(!rst) low_stop_to_high_stop_p_ec);

property low_stop_to_high_stop_1p_ec;
  low_stop_to_high_stop_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
low_stop_to_high_stop_1a_ec: assert property (disable iff(!rst) low_stop_to_high_stop_1p_ec);

property low_stop_to_high_stop_2p_ec;
  low_stop_to_high_stop_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
low_stop_to_high_stop_2a_ec: assert property (disable iff(!rst) low_stop_to_high_stop_2p_ec);


sequence high_stop_to_high_stop_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 11) &&
  (i2c_controller.count_thigh < THIGH);
endsequence

property high_stop_to_high_stop_p_ec;
  high_stop_to_high_stop_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_stop_to_high_stop_a_ec: assert property (disable iff(!rst) high_stop_to_high_stop_p_ec);

property high_stop_to_high_stop_1p_ec;
  high_stop_to_high_stop_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_stop_to_high_stop_1a_ec: assert property (disable iff(!rst) high_stop_to_high_stop_1p_ec);

property high_stop_to_high_stop_2p_ec;
  high_stop_to_high_stop_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_stop_to_high_stop_2a_ec: assert property (disable iff(!rst) high_stop_to_high_stop_2p_ec);


sequence high_stop_to_idle_p_sequence;
  (i2c_controller.i2c_controller_control_inst.current_state == 11) &&
  (i2c_controller.count_thigh >= THIGH);
endsequence

property high_stop_to_idle_p_ec;
  high_stop_to_idle_p_sequence
  |->
  ##1 i2c_controller.scl == SCL_tx;
endproperty
high_stop_to_idle_a_ec: assert property (disable iff(!rst) high_stop_to_idle_p_ec);

property high_stop_to_idle_1p_ec;
  high_stop_to_idle_p_sequence
  |->
  ##1 i2c_controller.sda_out == SDA_tx;
endproperty
high_stop_to_idle_1a_ec: assert property (disable iff(!rst) high_stop_to_idle_1p_ec);

property high_stop_to_idle_2p_ec;
  high_stop_to_idle_p_sequence
  |->
  ##1 i2c_controller.data_rcv == data_received;
endproperty
high_stop_to_idle_2a_ec: assert property (disable iff(!rst) high_stop_to_idle_2p_ec);

endmodule

