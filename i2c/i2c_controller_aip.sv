// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 26.03.2025 at 12:13                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import i2c_controller_pkg::*;


module fv_i2c_controller_m(
  input logic rst,
  input logic clk,

  // Ports
  input logic unsigned [0:0] start,

  input logic unsigned [0:0] scl,

  input logic unsigned [0:0] sda_out,

  input logic unsigned [0:0] sda_in,

  input logic unsigned [7:0] addr,

  input logic unsigned [23:0] data_snt,

  input logic unsigned [23:0] data_rcv,

  input logic unsigned [23:0] data_rcv_in,

  // Registers
  input logic unsigned [0:0] ack,
  input logic unsigned [7:0] addr_shift_reg,
  input logic unsigned [3:0] bit_count_addr,
  input logic unsigned [3:0] bit_count_data,
  input logic unsigned [9:0] count_thd,
  input logic unsigned [9:0] count_thigh,
  input logic unsigned [9:0] count_tlow,
  input logic unsigned [23:0] data_shift_reg,
  input logic unsigned [1:0] rcvd_byte,
  input logic unsigned [0:0] rw,
  input logic unsigned [1:0] sent_byte,

  // States
  input logic IDLE_S,
  input logic START_S,
  input logic LOW_CLK_ADDR_S,
  input logic HIGH_CLK_ADDR_S,
  input logic LOW_ADDR_ACK_S,
  input logic HIGH_ADDR_ACK_S,
  input logic LOW_CLK_DATA_S,
  input logic HIGH_CLK_DATA_S,
  input logic LOW_DATA_ACK_S,
  input logic HIGH_DATA_ACK_S,
  input logic LOW_STOP_S,
  input logic HIGH_STOP_S
);


default clocking default_clk @(posedge clk); endclocking


sequence reset_sequence;
  rst ##1 !rst;
endsequence


reset_a: assert property (reset_p);
property reset_p;
  reset_sequence |->
  IDLE_S &&
  ack == 1'd0 &&
  addr_shift_reg == 8'd0 &&
  bit_count_addr == 4'd0 &&
  bit_count_data == 4'd0 &&
  count_thd == 10'd0 &&
  count_thigh == 10'd0 &&
  count_tlow == 10'd0 &&
  data_rcv == 24'd0 &&
  data_shift_reg == 24'd0 &&
  rcvd_byte == 2'd0 &&
  rw == 1'd0 &&
  scl == 1'd1 &&
  sda_out == 1'd1 &&
  sent_byte == 2'd0;
endproperty


HIGH_ADDR_ACK_S_to_HIGH_ADDR_ACK_S_a: assert property (disable iff(rst) HIGH_ADDR_ACK_S_to_HIGH_ADDR_ACK_S_p);
property HIGH_ADDR_ACK_S_to_HIGH_ADDR_ACK_S_p;
  HIGH_ADDR_ACK_S &&
  1 &&
  (count_thigh == 10'd50)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_ADDR_ACK_S &&
  ack == $past(sda_in, 1) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_ADDR_ACK_S_to_HIGH_ADDR_ACK_S_1_a: assert property (disable iff(rst) HIGH_ADDR_ACK_S_to_HIGH_ADDR_ACK_S_1_p);
property HIGH_ADDR_ACK_S_to_HIGH_ADDR_ACK_S_1_p;
  HIGH_ADDR_ACK_S &&
  (({ 54'h0, count_thigh} ) < 64'd225) &&
  (count_thigh != 10'd50)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_ADDR_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_ADDR_ACK_S_to_LOW_CLK_DATA_S_a: assert property (disable iff(rst) HIGH_ADDR_ACK_S_to_LOW_CLK_DATA_S_p);
property HIGH_ADDR_ACK_S_to_LOW_CLK_DATA_S_p;
  HIGH_ADDR_ACK_S &&
  (({ 54'h0, count_thigh} ) >= 64'd225)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_CLK_DATA_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  bit_count_data == 4'd0 &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_CLK_ADDR_S_to_HIGH_CLK_ADDR_S_a: assert property (disable iff(rst) HIGH_CLK_ADDR_S_to_HIGH_CLK_ADDR_S_p);
property HIGH_CLK_ADDR_S_to_HIGH_CLK_ADDR_S_p;
  HIGH_CLK_ADDR_S &&
  (({ 54'h0, count_thigh} ) < 64'd225)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_CLK_ADDR_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_CLK_ADDR_S_to_LOW_ADDR_ACK_S_a: assert property (disable iff(rst) HIGH_CLK_ADDR_S_to_LOW_ADDR_ACK_S_p);
property HIGH_CLK_ADDR_S_to_LOW_ADDR_ACK_S_p;
  HIGH_CLK_ADDR_S &&
  (({ 54'h0, count_thigh} ) >= 64'd225) &&
  (({ 60'h0, bit_count_addr} ) >= 64'd8)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_ADDR_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_CLK_ADDR_S_to_LOW_CLK_ADDR_S_a: assert property (disable iff(rst) HIGH_CLK_ADDR_S_to_LOW_CLK_ADDR_S_p);
property HIGH_CLK_ADDR_S_to_LOW_CLK_ADDR_S_p;
  HIGH_CLK_ADDR_S &&
  (({ 54'h0, count_thigh} ) >= 64'd225) &&
  (({ 60'h0, bit_count_addr} ) < 64'd8)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_CLK_ADDR_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_CLK_DATA_S_to_HIGH_CLK_DATA_S_a: assert property (disable iff(rst) HIGH_CLK_DATA_S_to_HIGH_CLK_DATA_S_p);
property HIGH_CLK_DATA_S_to_HIGH_CLK_DATA_S_p;
  HIGH_CLK_DATA_S &&
  1 &&
  (count_thigh == 10'd50) &&
  (rw != 1'd0)
|->
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_CLK_DATA_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  bit_count_data == (4'd1 + $past(bit_count_data, 1)) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  data_rcv == (({ { $past(data_rcv_in, 1) }[22:0], 1'h0} ) | 24'($past(sda_in, 1))) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_CLK_DATA_S_to_HIGH_CLK_DATA_S_1_a: assert property (disable iff(rst) HIGH_CLK_DATA_S_to_HIGH_CLK_DATA_S_1_p);
property HIGH_CLK_DATA_S_to_HIGH_CLK_DATA_S_1_p;
  HIGH_CLK_DATA_S &&
  (({ 54'd0, count_thigh} ) < 64'd225) &&
  !((count_thigh == 10'd50) && (rw != 1'd0))
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_CLK_DATA_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_CLK_DATA_S_to_LOW_CLK_DATA_S_a: assert property (disable iff(rst) HIGH_CLK_DATA_S_to_LOW_CLK_DATA_S_p);
property HIGH_CLK_DATA_S_to_LOW_CLK_DATA_S_p;
  HIGH_CLK_DATA_S &&
  (({ 54'h0, count_thigh} ) >= 64'd225) &&
  (({ 60'h0, bit_count_data} ) < 64'd8)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_CLK_DATA_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_CLK_DATA_S_to_LOW_DATA_ACK_S_a: assert property (disable iff(rst) HIGH_CLK_DATA_S_to_LOW_DATA_ACK_S_p);
property HIGH_CLK_DATA_S_to_LOW_DATA_ACK_S_p;
  HIGH_CLK_DATA_S &&
  (({ 54'h0, count_thigh} ) >= 64'd225) &&
  (({ 60'h0, bit_count_data} ) >= 64'd8)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_DATA_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_DATA_ACK_S_to_HIGH_DATA_ACK_S_a: assert property (disable iff(rst) HIGH_DATA_ACK_S_to_HIGH_DATA_ACK_S_p);
property HIGH_DATA_ACK_S_to_HIGH_DATA_ACK_S_p;
  HIGH_DATA_ACK_S &&
  1 &&
  (count_thigh == 10'd50) &&
  (rw == 1'd0)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_DATA_ACK_S &&
  ack == $past(sda_in, 1) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  bit_count_data == 4'd0 &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  sent_byte == (2'd1 + $past(sent_byte, 1));
endproperty


HIGH_DATA_ACK_S_to_HIGH_DATA_ACK_S_1_a: assert property (disable iff(rst) HIGH_DATA_ACK_S_to_HIGH_DATA_ACK_S_1_p);
property HIGH_DATA_ACK_S_to_HIGH_DATA_ACK_S_1_p;
  HIGH_DATA_ACK_S &&
  (({ 54'd0, count_thigh} ) < 64'd225) &&
  !((count_thigh == 10'd50) && (rw == 1'd0))
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_DATA_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  bit_count_data == 4'd0 &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_DATA_ACK_S_to_LOW_CLK_DATA_S_a: assert property (disable iff(rst) HIGH_DATA_ACK_S_to_LOW_CLK_DATA_S_p);
property HIGH_DATA_ACK_S_to_LOW_CLK_DATA_S_p;
  HIGH_DATA_ACK_S &&
  (({ 54'd0, count_thigh} ) >= 64'd225) &&
  !((rw == 1'd1) && (rcvd_byte == 2'd3)) &&
  !((rw == 1'd0) && (sent_byte == 2'd3))
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_CLK_DATA_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_DATA_ACK_S_to_LOW_STOP_S_a: assert property (disable iff(rst) HIGH_DATA_ACK_S_to_LOW_STOP_S_p);
property HIGH_DATA_ACK_S_to_LOW_STOP_S_p;
  HIGH_DATA_ACK_S &&
  (({ 54'd0, count_thigh} ) >= 64'd225) &&
  (((rw == 1'd1) && (rcvd_byte == 2'd3)) || ((rw == 1'd0) && (sent_byte == 2'd3)))
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_STOP_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_STOP_S_to_HIGH_STOP_S_a: assert property (disable iff(rst) HIGH_STOP_S_to_HIGH_STOP_S_p);
property HIGH_STOP_S_to_HIGH_STOP_S_p;
  HIGH_STOP_S &&
  (({ 54'h0, count_thigh} ) < 64'd225) &&
  (count_thigh != 10'd225)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_STOP_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


HIGH_STOP_S_to_IDLE_S_a: assert property (disable iff(rst) HIGH_STOP_S_to_IDLE_S_p);
property HIGH_STOP_S_to_IDLE_S_p;
  HIGH_STOP_S &&
  (({ 54'h0, count_thigh} ) >= 64'd225)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  IDLE_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == (10'd1 + $past(count_thigh, 1)) &&
  count_tlow == 10'd0 &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  sda_out == 1'd1 &&
  $stable(sent_byte);
endproperty


IDLE_S_to_IDLE_S_a: assert property (disable iff(rst) IDLE_S_to_IDLE_S_p);
property IDLE_S_to_IDLE_S_p;
  IDLE_S &&
  (start == 1'd0)
|->
  ##1
  IDLE_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  bit_count_addr == 4'd0 &&
  bit_count_data == 4'd0 &&
  count_thd == 10'd0 &&
  count_thigh == 10'd0 &&
  $stable(count_tlow) &&
  data_rcv == 24'd0 &&
  $stable(data_shift_reg) &&
  rcvd_byte == 2'd0 &&
  rw == 1'd0 &&
  scl == 1'd1 &&
  sda_out == 1'd1 &&
  sent_byte == 2'd0;
endproperty


IDLE_S_to_START_S_a: assert property (disable iff(rst) IDLE_S_to_START_S_p);
property IDLE_S_to_START_S_p;
  IDLE_S &&
  (start != 1'd0)
|->
  ##1 ($stable(scl)) and
  ##1
  START_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  bit_count_addr == 4'd0 &&
  bit_count_data == 4'd0 &&
  count_thd == 10'd0 &&
  count_thigh == 10'd0 &&
  $stable(count_tlow) &&
  data_rcv == 24'd0 &&
  $stable(data_shift_reg) &&
  rcvd_byte == 2'd0 &&
  rw == 1'd0 &&
  sda_out == 1'd1 &&
  sent_byte == 2'd0;
endproperty


LOW_ADDR_ACK_S_to_HIGH_ADDR_ACK_S_a: assert property (disable iff(rst) LOW_ADDR_ACK_S_to_HIGH_ADDR_ACK_S_p);
property LOW_ADDR_ACK_S_to_HIGH_ADDR_ACK_S_p;
  LOW_ADDR_ACK_S &&
  (({ 54'h0, count_tlow} ) >= 64'd250)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  HIGH_ADDR_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  $stable(count_tlow) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  sda_out == 1'd1 &&
  $stable(sent_byte);
endproperty


LOW_ADDR_ACK_S_to_LOW_ADDR_ACK_S_a: assert property (disable iff(rst) LOW_ADDR_ACK_S_to_LOW_ADDR_ACK_S_p);
property LOW_ADDR_ACK_S_to_LOW_ADDR_ACK_S_p;
  LOW_ADDR_ACK_S &&
  (({ 54'h0, count_tlow} ) < 64'd250)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  LOW_ADDR_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  sda_out == 1'd1 &&
  $stable(sent_byte);
endproperty


LOW_CLK_ADDR_S_to_HIGH_CLK_ADDR_S_a: assert property (disable iff(rst) LOW_CLK_ADDR_S_to_HIGH_CLK_ADDR_S_p);
property LOW_CLK_ADDR_S_to_HIGH_CLK_ADDR_S_p;
  LOW_CLK_ADDR_S &&
  (({ 54'h0, count_tlow} ) >= 64'd250)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_CLK_ADDR_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  $stable(count_tlow) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


LOW_CLK_ADDR_S_to_LOW_CLK_ADDR_S_a: assert property (disable iff(rst) LOW_CLK_ADDR_S_to_LOW_CLK_ADDR_S_p);
property LOW_CLK_ADDR_S_to_LOW_CLK_ADDR_S_p;
  LOW_CLK_ADDR_S &&
  1 &&
  (count_tlow == 10'd150)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  LOW_CLK_ADDR_S &&
  $stable(ack) &&
  addr_shift_reg == ({ { $past(addr_shift_reg, 1) }[6:0], 1'h0} ) &&
  bit_count_addr == (4'd1 + $past(bit_count_addr, 1)) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  sda_out == { $past(addr_shift_reg, 1) }[7] &&
  $stable(sent_byte);
endproperty


LOW_CLK_ADDR_S_to_LOW_CLK_ADDR_S_1_a: assert property (disable iff(rst) LOW_CLK_ADDR_S_to_LOW_CLK_ADDR_S_1_p);
property LOW_CLK_ADDR_S_to_LOW_CLK_ADDR_S_1_p;
  LOW_CLK_ADDR_S &&
  (({ 54'h0, count_tlow} ) < 64'd250) &&
  (count_tlow != 10'd150)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_CLK_ADDR_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  $stable(sent_byte);
endproperty


LOW_CLK_DATA_S_to_HIGH_CLK_DATA_S_a: assert property (disable iff(rst) LOW_CLK_DATA_S_to_HIGH_CLK_DATA_S_p);
property LOW_CLK_DATA_S_to_HIGH_CLK_DATA_S_p;
  LOW_CLK_DATA_S &&
  (ack == 1'd0) &&
  (({ 54'd0, count_tlow} ) >= 64'd250)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_CLK_DATA_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  $stable(count_tlow) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


LOW_CLK_DATA_S_to_LOW_CLK_DATA_S_a: assert property (disable iff(rst) LOW_CLK_DATA_S_to_LOW_CLK_DATA_S_p);
property LOW_CLK_DATA_S_to_LOW_CLK_DATA_S_p;
  LOW_CLK_DATA_S &&
  (ack == 1'd0) &&
  1 &&
  (count_tlow == 10'd150) &&
  (rw == 1'd0)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  LOW_CLK_DATA_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  bit_count_data == (4'd1 + $past(bit_count_data, 1)) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  data_shift_reg == ({ { $past(data_shift_reg, 1) }[22:0], 1'h0} ) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  sda_out == { $past(data_shift_reg, 1) }[23] &&
  $stable(sent_byte);
endproperty


LOW_CLK_DATA_S_to_LOW_CLK_DATA_S_1_a: assert property (disable iff(rst) LOW_CLK_DATA_S_to_LOW_CLK_DATA_S_1_p);
property LOW_CLK_DATA_S_to_LOW_CLK_DATA_S_1_p;
  LOW_CLK_DATA_S &&
  (ack == 1'd0) &&
  (({ 54'd0, count_tlow} ) < 64'd250) &&
  (rw == 1'd1)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  LOW_CLK_DATA_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  sda_out == 1'd1 &&
  $stable(sent_byte);
endproperty


LOW_CLK_DATA_S_to_LOW_CLK_DATA_S_2_a: assert property (disable iff(rst) LOW_CLK_DATA_S_to_LOW_CLK_DATA_S_2_p);
property LOW_CLK_DATA_S_to_LOW_CLK_DATA_S_2_p;
  LOW_CLK_DATA_S &&
  (ack == 1'd0) &&
  (({ 54'd0, count_tlow} ) < 64'd250) &&
  (count_tlow != 10'd150) &&
  (rw != 1'd1)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_CLK_DATA_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  $stable(sent_byte);
endproperty


LOW_CLK_DATA_S_to_LOW_STOP_S_a: assert property (disable iff(rst) LOW_CLK_DATA_S_to_LOW_STOP_S_p);
property LOW_CLK_DATA_S_to_LOW_STOP_S_p;
  LOW_CLK_DATA_S &&
  (ack != 1'd0)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_STOP_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  $stable(sent_byte);
endproperty


LOW_DATA_ACK_S_to_HIGH_DATA_ACK_S_a: assert property (disable iff(rst) LOW_DATA_ACK_S_to_HIGH_DATA_ACK_S_p);
property LOW_DATA_ACK_S_to_HIGH_DATA_ACK_S_p;
  LOW_DATA_ACK_S &&
  (({ 54'h0, count_tlow} ) >= 64'd250)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_DATA_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  $stable(count_tlow) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_a: assert property (disable iff(rst) LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_p);
property LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_p;
  LOW_DATA_ACK_S &&
  1 &&
  (count_tlow == 10'd150) &&
  (rw == 1'd1) &&
  (rcvd_byte != 2'h2)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  LOW_DATA_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  rcvd_byte == (2'd1 + $past(rcvd_byte, 1)) &&
  $stable(rw) &&
  scl == 1'd0 &&
  sda_out == 1'd0 &&
  $stable(sent_byte);
endproperty


LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_1_a: assert property (disable iff(rst) LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_1_p);
property LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_1_p;
  LOW_DATA_ACK_S &&
  1 &&
  (count_tlow == 10'd150) &&
  (rw == 1'd1) &&
  (rcvd_byte == 2'h2)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  LOW_DATA_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  rcvd_byte == (2'd1 + $past(rcvd_byte, 1)) &&
  $stable(rw) &&
  scl == 1'd0 &&
  sda_out == 1'd1 &&
  $stable(sent_byte);
endproperty


LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_2_a: assert property (disable iff(rst) LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_2_p);
property LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_2_p;
  LOW_DATA_ACK_S &&
  (({ 54'd0, count_tlow} ) < 64'd250) &&
  (rw == 1'd0)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  LOW_DATA_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  sda_out == 1'd1 &&
  $stable(sent_byte);
endproperty


LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_3_a: assert property (disable iff(rst) LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_3_p);
property LOW_DATA_ACK_S_to_LOW_DATA_ACK_S_3_p;
  LOW_DATA_ACK_S &&
  (({ 54'd0, count_tlow} ) < 64'd250) &&
  (count_tlow != 10'd150) &&
  (rw != 1'd0)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_DATA_ACK_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  $stable(sent_byte);
endproperty


LOW_STOP_S_to_HIGH_STOP_S_a: assert property (disable iff(rst) LOW_STOP_S_to_HIGH_STOP_S_p);
property LOW_STOP_S_to_HIGH_STOP_S_p;
  LOW_STOP_S &&
  (({ 54'h0, count_tlow} ) >= 64'd250)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  HIGH_STOP_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  $stable(count_tlow) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd1 &&
  $stable(sent_byte);
endproperty


LOW_STOP_S_to_LOW_STOP_S_a: assert property (disable iff(rst) LOW_STOP_S_to_LOW_STOP_S_p);
property LOW_STOP_S_to_LOW_STOP_S_p;
  LOW_STOP_S &&
  1 &&
  (count_tlow == 10'd150)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  LOW_STOP_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  sda_out == 1'd0 &&
  $stable(sent_byte);
endproperty


LOW_STOP_S_to_LOW_STOP_S_1_a: assert property (disable iff(rst) LOW_STOP_S_to_LOW_STOP_S_1_p);
property LOW_STOP_S_to_LOW_STOP_S_1_p;
  LOW_STOP_S &&
  (({ 54'h0, count_tlow} ) < 64'd250) &&
  (count_tlow != 10'd150)
|->
  ##1 ($stable(data_rcv)) and
  ##1 ($stable(sda_out)) and
  ##1
  LOW_STOP_S &&
  $stable(ack) &&
  $stable(addr_shift_reg) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  $stable(count_thd) &&
  count_thigh == 10'd0 &&
  count_tlow == (10'd1 + $past(count_tlow, 1)) &&
  $stable(data_shift_reg) &&
  $stable(rcvd_byte) &&
  $stable(rw) &&
  scl == 1'd0 &&
  $stable(sent_byte);
endproperty


START_S_to_LOW_CLK_ADDR_S_a: assert property (disable iff(rst) START_S_to_LOW_CLK_ADDR_S_p);
property START_S_to_LOW_CLK_ADDR_S_p;
  START_S &&
  (({ 54'h0, count_thd} ) >= 64'd225)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  LOW_CLK_ADDR_S &&
  $stable(ack) &&
  addr_shift_reg == $past(addr, 1) &&
  bit_count_addr == 4'd0 &&
  $stable(bit_count_data) &&
  count_thd == (10'd1 + $past(count_thd, 1)) &&
  $stable(count_thigh) &&
  count_tlow == 10'd0 &&
  data_shift_reg == $past(data_snt, 1) &&
  rcvd_byte == 2'd0 &&
  rw == { $past(addr, 1) }[0] &&
  scl == 1'd1 &&
  sda_out == 1'd0 &&
  sent_byte == 2'd0;
endproperty


START_S_to_START_S_a: assert property (disable iff(rst) START_S_to_START_S_p);
property START_S_to_START_S_p;
  START_S &&
  (({ 54'h0, count_thd} ) < 64'd225)
|->
  ##1 ($stable(data_rcv)) and
  ##1
  START_S &&
  $stable(ack) &&
  addr_shift_reg == $past(addr, 1) &&
  $stable(bit_count_addr) &&
  $stable(bit_count_data) &&
  count_thd == (10'd1 + $past(count_thd, 1)) &&
  $stable(count_thigh) &&
  $stable(count_tlow) &&
  data_shift_reg == $past(data_snt, 1) &&
  rcvd_byte == 2'd0 &&
  rw == { $past(addr, 1) }[0] &&
  scl == 1'd1 &&
  sda_out == 1'd0 &&
  sent_byte == 2'd0;
endproperty


parameter SANITY = 1;
if (SANITY) begin
// Check that no more than 1 state condition is met at the same time
  sanity_onehot0_state: assert property ( $onehot0({HIGH_ADDR_ACK_S, HIGH_CLK_ADDR_S, HIGH_CLK_DATA_S, HIGH_DATA_ACK_S, HIGH_STOP_S, IDLE_S, LOW_ADDR_ACK_S, LOW_CLK_ADDR_S, LOW_CLK_DATA_S, LOW_DATA_ACK_S, LOW_STOP_S, START_S}) );
end

property SDA_constraints_p;
   (master_I2C.SDA_tx == 1'd1)
|->
    sda_in == 1'd1 ||
    sda_in == 1'd0;
endproperty
run_SDA_constraints_a: assume property (disable iff(rst) SDA_constraints_p);

property num_bytes_send_p;
   master_I2C.num_bytes_send == 'h3 &&
   master_I2C.num_bytes_receive == 'h3;
endproperty
num_bytes_send_a: assume property (disable iff(rst) num_bytes_send_p);

property stable_addr_p;
   $stable(master_I2C.addr_target) &&
   $stable(master_I2C.data_send);
endproperty
stable_addr_a: assume property (disable iff(rst) stable_addr_p);

endmodule
