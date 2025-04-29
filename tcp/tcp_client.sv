// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 04.02.2025 at 12:06                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import tcp_client_pkg::*;


module fv_tcp_client_m(
  input logic rst,
  input logic clk,

  // Ports
  input st_TCP_Header TCP_in,

  input st_TCP_Header TCP_out,

  // Registers
  input e_events ev,
  input st_TCP_Header t_out,

  // States
  input logic CLOSED_S,
  input logic LISTEN_S,
  input logic SYN_SENT_S,
  input logic SYN_RCVD_S,
  input logic ESTABLISHED_S,
  input logic FIN_WAIT_1_S,
  input logic CLOSE_WAIT_S,
  input logic CLOSING_S,
  input logic FIN_WAIT_2_S,
  input logic LAST_ACK_S,
  input logic TIME_WAIT_S
);


default clocking default_clk @(posedge clk); endclocking


st_TCP_Header TCP_out_0_i;
assign TCP_out_0_i = '{
  source_port: 16'd0,
  destination_port: 16'd0,
  seq_number: 0,
  ack_number: 0,
  data_offset: 4'd0,
  URG: 0,
  ACK: 0,
  PSH: 0,
  RST: 0,
  SYN: 0,
  FIN: 0,
  checksum: 16'd0,
  urgent_pointer: 16'd0
};

st_TCP_Header TCP_out_1_i;
assign TCP_out_1_i = '{
  source_port: t_out.source_port,
  destination_port: t_out.destination_port,
  seq_number: 2000,
  ack_number: 32'((64'd1 + ({ 'h0, TCP_in.seq_number} ))),
  data_offset: t_out.data_offset,
  URG: t_out.URG,
  ACK: 1,
  PSH: t_out.PSH,
  RST: t_out.RST,
  SYN: 1,
  FIN: t_out.FIN,
  checksum: t_out.checksum,
  urgent_pointer: t_out.urgent_pointer
};

st_TCP_Header TCP_out_2_i;
assign TCP_out_2_i = '{
  source_port: t_out.source_port,
  destination_port: t_out.destination_port,
  seq_number: TCP_in.ack_number,
  ack_number: t_out.ack_number,
  data_offset: t_out.data_offset,
  URG: t_out.URG,
  ACK: 1,
  PSH: 1,
  RST: t_out.RST,
  SYN: t_out.SYN,
  FIN: t_out.FIN,
  checksum: t_out.checksum,
  urgent_pointer: t_out.urgent_pointer
};


sequence reset_sequence;
  rst ##1 !rst;
endsequence


property run_reset_p;
  reset_sequence |->
  CLOSED_S &&
  TCP_out == TCP_out_0_i &&
  t_out == TCP_out_0_i;
endproperty
run_reset_a: assert property (run_reset_p);


property run_CLOSED_S_to_CLOSED_S_p;
  CLOSED_S &&
  (ev != ACTIVE_OPEN) &&
  (ev != PASSIVE_OPEN)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  CLOSED_S &&
  $stable(t_out);
endproperty
run_CLOSED_S_to_CLOSED_S_a: assert property (disable iff(rst) run_CLOSED_S_to_CLOSED_S_p);


property run_CLOSED_S_to_LISTEN_S_p;
  CLOSED_S &&
  (ev == PASSIVE_OPEN)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  LISTEN_S &&
  $stable(t_out);
endproperty
run_CLOSED_S_to_LISTEN_S_a: assert property (disable iff(rst) run_CLOSED_S_to_LISTEN_S_p);


property run_CLOSED_S_to_SYN_SENT_S_p;
  CLOSED_S &&
  (ev == ACTIVE_OPEN)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  SYN_SENT_S &&
  $stable(t_out);
endproperty
run_CLOSED_S_to_SYN_SENT_S_a: assert property (disable iff(rst) run_CLOSED_S_to_SYN_SENT_S_p);


property run_CLOSE_WAIT_S_to_CLOSE_WAIT_S_p;
  CLOSE_WAIT_S &&
  (ev != CLOSE)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  CLOSE_WAIT_S &&
  $stable(t_out);
endproperty
run_CLOSE_WAIT_S_to_CLOSE_WAIT_S_a: assert property (disable iff(rst) run_CLOSE_WAIT_S_to_CLOSE_WAIT_S_p);


property run_CLOSE_WAIT_S_to_LAST_ACK_S_p;
  CLOSE_WAIT_S &&
  (ev == CLOSE)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  LAST_ACK_S &&
  $stable(t_out);
endproperty
run_CLOSE_WAIT_S_to_LAST_ACK_S_a: assert property (disable iff(rst) run_CLOSE_WAIT_S_to_LAST_ACK_S_p);


property run_CLOSING_S_to_CLOSING_S_p;
  CLOSING_S &&
  (ev != RECEIVE_FIN_ACK)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  CLOSING_S &&
  $stable(t_out);
endproperty
run_CLOSING_S_to_CLOSING_S_a: assert property (disable iff(rst) run_CLOSING_S_to_CLOSING_S_p);


property run_CLOSING_S_to_TIME_WAIT_S_p;
  CLOSING_S &&
  (ev == RECEIVE_FIN_ACK)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  TIME_WAIT_S &&
  $stable(t_out);
endproperty
run_CLOSING_S_to_TIME_WAIT_S_a: assert property (disable iff(rst) run_CLOSING_S_to_TIME_WAIT_S_p);


property run_ESTABLISHED_S_to_CLOSE_WAIT_S_p;
  ESTABLISHED_S &&
  (ev == RECEIVE_FIN)
|->
  ##1
  CLOSE_WAIT_S &&
  TCP_out == $past(TCP_out_2_i, 1) &&
  t_out == $past(TCP_out_2_i, 1);
endproperty
run_ESTABLISHED_S_to_CLOSE_WAIT_S_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_CLOSE_WAIT_S_p);


property run_ESTABLISHED_S_to_ESTABLISHED_S_p;
  ESTABLISHED_S &&
  (ev != RECEIVE_FIN) &&
  (ev != CLOSE)
|->
  ##1
  ESTABLISHED_S &&
  TCP_out == $past(TCP_out_2_i, 1) &&
  t_out == $past(TCP_out_2_i, 1);
endproperty
run_ESTABLISHED_S_to_ESTABLISHED_S_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_ESTABLISHED_S_p);


property run_ESTABLISHED_S_to_FIN_WAIT_1_S_p;
  ESTABLISHED_S &&
  (ev == CLOSE)
|->
  ##1
  FIN_WAIT_1_S &&
  TCP_out == $past(TCP_out_2_i, 1) &&
  t_out == $past(TCP_out_2_i, 1);
endproperty
run_ESTABLISHED_S_to_FIN_WAIT_1_S_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_FIN_WAIT_1_S_p);


property run_FIN_WAIT_1_S_to_CLOSING_S_p;
  FIN_WAIT_1_S &&
  (ev == RECEIVE_FIN)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  CLOSING_S &&
  $stable(t_out);
endproperty
run_FIN_WAIT_1_S_to_CLOSING_S_a: assert property (disable iff(rst) run_FIN_WAIT_1_S_to_CLOSING_S_p);


property run_FIN_WAIT_1_S_to_FIN_WAIT_1_S_p;
  FIN_WAIT_1_S &&
  (ev != RECEIVE_FIN) &&
  (ev != RECEIVE_FIN_ACK)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  FIN_WAIT_1_S &&
  $stable(t_out);
endproperty
run_FIN_WAIT_1_S_to_FIN_WAIT_1_S_a: assert property (disable iff(rst) run_FIN_WAIT_1_S_to_FIN_WAIT_1_S_p);


property run_FIN_WAIT_1_S_to_FIN_WAIT_2_S_p;
  FIN_WAIT_1_S &&
  (ev == RECEIVE_FIN_ACK)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  FIN_WAIT_2_S &&
  $stable(t_out);
endproperty
run_FIN_WAIT_1_S_to_FIN_WAIT_2_S_a: assert property (disable iff(rst) run_FIN_WAIT_1_S_to_FIN_WAIT_2_S_p);


property run_FIN_WAIT_2_S_to_FIN_WAIT_2_S_p;
  FIN_WAIT_2_S &&
  (ev != RECEIVE_FIN)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  FIN_WAIT_2_S &&
  $stable(t_out);
endproperty
run_FIN_WAIT_2_S_to_FIN_WAIT_2_S_a: assert property (disable iff(rst) run_FIN_WAIT_2_S_to_FIN_WAIT_2_S_p);


property run_FIN_WAIT_2_S_to_TIME_WAIT_S_p;
  FIN_WAIT_2_S &&
  (ev == RECEIVE_FIN)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  TIME_WAIT_S &&
  $stable(t_out);
endproperty
run_FIN_WAIT_2_S_to_TIME_WAIT_S_a: assert property (disable iff(rst) run_FIN_WAIT_2_S_to_TIME_WAIT_S_p);


property run_LAST_ACK_S_to_CLOSED_S_p;
  LAST_ACK_S &&
  (ev == RECEIVE_FIN_ACK)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  CLOSED_S &&
  $stable(t_out);
endproperty
run_LAST_ACK_S_to_CLOSED_S_a: assert property (disable iff(rst) run_LAST_ACK_S_to_CLOSED_S_p);


property run_LAST_ACK_S_to_LAST_ACK_S_p;
  LAST_ACK_S &&
  (ev != RECEIVE_FIN_ACK)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  LAST_ACK_S &&
  $stable(t_out);
endproperty
run_LAST_ACK_S_to_LAST_ACK_S_a: assert property (disable iff(rst) run_LAST_ACK_S_to_LAST_ACK_S_p);


property run_LISTEN_S_to_CLOSED_S_p;
  LISTEN_S &&
  (ev == CLOSE)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  CLOSED_S &&
  $stable(t_out);
endproperty
run_LISTEN_S_to_CLOSED_S_a: assert property (disable iff(rst) run_LISTEN_S_to_CLOSED_S_p);


property run_LISTEN_S_to_LISTEN_S_p;
  LISTEN_S &&
  (ev != SEND) &&
  (ev != RECEIVE_SYN) &&
  (ev != CLOSE)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  LISTEN_S &&
  $stable(t_out);
endproperty
run_LISTEN_S_to_LISTEN_S_a: assert property (disable iff(rst) run_LISTEN_S_to_LISTEN_S_p);


property run_LISTEN_S_to_SYN_RCVD_S_p;
  LISTEN_S &&
  (ev == RECEIVE_SYN)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  SYN_RCVD_S &&
  $stable(t_out);
endproperty
run_LISTEN_S_to_SYN_RCVD_S_a: assert property (disable iff(rst) run_LISTEN_S_to_SYN_RCVD_S_p);


property run_LISTEN_S_to_SYN_SENT_S_p;
  LISTEN_S &&
  (ev == SEND)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  SYN_SENT_S &&
  $stable(t_out);
endproperty
run_LISTEN_S_to_SYN_SENT_S_a: assert property (disable iff(rst) run_LISTEN_S_to_SYN_SENT_S_p);


property run_SYN_RCVD_S_to_ESTABLISHED_S_p;
  SYN_RCVD_S &&
  (ev == RECEIVE_SYN_ACK)
|->
  ##1
  ESTABLISHED_S &&
  TCP_out == $past(TCP_out_1_i, 1) &&
  t_out == $past(TCP_out_1_i, 1);
endproperty
run_SYN_RCVD_S_to_ESTABLISHED_S_a: assert property (disable iff(rst) run_SYN_RCVD_S_to_ESTABLISHED_S_p);


property run_SYN_RCVD_S_to_FIN_WAIT_1_S_p;
  SYN_RCVD_S &&
  (ev == CLOSE)
|->
  ##1
  FIN_WAIT_1_S &&
  TCP_out == $past(TCP_out_1_i, 1) &&
  t_out == $past(TCP_out_1_i, 1);
endproperty
run_SYN_RCVD_S_to_FIN_WAIT_1_S_a: assert property (disable iff(rst) run_SYN_RCVD_S_to_FIN_WAIT_1_S_p);


property run_SYN_RCVD_S_to_LISTEN_S_p;
  SYN_RCVD_S &&
  (ev == RECEIVE_RST)
|->
  ##1
  LISTEN_S &&
  TCP_out == $past(TCP_out_1_i, 1) &&
  t_out == $past(TCP_out_1_i, 1);
endproperty
run_SYN_RCVD_S_to_LISTEN_S_a: assert property (disable iff(rst) run_SYN_RCVD_S_to_LISTEN_S_p);


property run_SYN_RCVD_S_to_SYN_RCVD_S_p;
  SYN_RCVD_S &&
  (ev != RECEIVE_RST) &&
  (ev != RECEIVE_SYN_ACK) &&
  (ev != CLOSE)
|->
  ##1
  SYN_RCVD_S &&
  TCP_out == $past(TCP_out_1_i, 1) &&
  t_out == $past(TCP_out_1_i, 1);
endproperty
run_SYN_RCVD_S_to_SYN_RCVD_S_a: assert property (disable iff(rst) run_SYN_RCVD_S_to_SYN_RCVD_S_p);


property run_SYN_SENT_S_to_CLOSED_S_p;
  SYN_SENT_S &&
  (ev != RECEIVE_SYN) &&
  (ev != RECEIVE_SYN_ACK)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  CLOSED_S &&
  $stable(t_out);
endproperty
run_SYN_SENT_S_to_CLOSED_S_a: assert property (disable iff(rst) run_SYN_SENT_S_to_CLOSED_S_p);


property run_SYN_SENT_S_to_ESTABLISHED_S_p;
  SYN_SENT_S &&
  (ev == RECEIVE_SYN_ACK)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  ESTABLISHED_S &&
  $stable(t_out);
endproperty
run_SYN_SENT_S_to_ESTABLISHED_S_a: assert property (disable iff(rst) run_SYN_SENT_S_to_ESTABLISHED_S_p);


property run_SYN_SENT_S_to_SYN_RCVD_S_p;
  SYN_SENT_S &&
  (ev == RECEIVE_SYN)
|->
  ##1 ($stable(TCP_out)) and
  ##1
  SYN_RCVD_S &&
  $stable(t_out);
endproperty
run_SYN_SENT_S_to_SYN_RCVD_S_a: assert property (disable iff(rst) run_SYN_SENT_S_to_SYN_RCVD_S_p);


property run_TIME_WAIT_S_to_CLOSED_S_p;
  TIME_WAIT_S
|->
  ##1 ($stable(TCP_out)) and
  ##1
  CLOSED_S &&
  $stable(t_out);
endproperty
run_TIME_WAIT_S_to_CLOSED_S_a: assert property (disable iff(rst) run_TIME_WAIT_S_to_CLOSED_S_p);


property run_CLOSED_S_eventually_left_p;
  CLOSED_S
|->
  s_eventually(!CLOSED_S);
endproperty
run_CLOSED_S_eventually_left_a: assert property (disable iff(rst) run_CLOSED_S_eventually_left_p);


property run_LISTEN_S_eventually_left_p;
  LISTEN_S
|->
  s_eventually(!LISTEN_S);
endproperty
run_LISTEN_S_eventually_left_a: assert property (disable iff(rst) run_LISTEN_S_eventually_left_p);


property run_SYN_SENT_S_eventually_left_p;
  SYN_SENT_S
|->
  s_eventually(!SYN_SENT_S);
endproperty
run_SYN_SENT_S_eventually_left_a: assert property (disable iff(rst) run_SYN_SENT_S_eventually_left_p);


property run_SYN_RCVD_S_eventually_left_p;
  SYN_RCVD_S
|->
  s_eventually(!SYN_RCVD_S);
endproperty
run_SYN_RCVD_S_eventually_left_a: assert property (disable iff(rst) run_SYN_RCVD_S_eventually_left_p);


property run_ESTABLISHED_S_eventually_left_p;
  ESTABLISHED_S
|->
  s_eventually(!ESTABLISHED_S);
endproperty
run_ESTABLISHED_S_eventually_left_a: assert property (disable iff(rst) run_ESTABLISHED_S_eventually_left_p);


property run_FIN_WAIT_1_S_eventually_left_p;
  FIN_WAIT_1_S
|->
  s_eventually(!FIN_WAIT_1_S);
endproperty
run_FIN_WAIT_1_S_eventually_left_a: assert property (disable iff(rst) run_FIN_WAIT_1_S_eventually_left_p);


property run_CLOSE_WAIT_S_eventually_left_p;
  CLOSE_WAIT_S
|->
  s_eventually(!CLOSE_WAIT_S);
endproperty
run_CLOSE_WAIT_S_eventually_left_a: assert property (disable iff(rst) run_CLOSE_WAIT_S_eventually_left_p);


property run_CLOSING_S_eventually_left_p;
  CLOSING_S
|->
  s_eventually(!CLOSING_S);
endproperty
run_CLOSING_S_eventually_left_a: assert property (disable iff(rst) run_CLOSING_S_eventually_left_p);


property run_FIN_WAIT_2_S_eventually_left_p;
  FIN_WAIT_2_S
|->
  s_eventually(!FIN_WAIT_2_S);
endproperty
run_FIN_WAIT_2_S_eventually_left_a: assert property (disable iff(rst) run_FIN_WAIT_2_S_eventually_left_p);


property run_LAST_ACK_S_eventually_left_p;
  LAST_ACK_S
|->
  s_eventually(!LAST_ACK_S);
endproperty
run_LAST_ACK_S_eventually_left_a: assert property (disable iff(rst) run_LAST_ACK_S_eventually_left_p);


property run_TIME_WAIT_S_eventually_left_p;
  TIME_WAIT_S
|->
  s_eventually(!TIME_WAIT_S);
endproperty
run_TIME_WAIT_S_eventually_left_a: assert property (disable iff(rst) run_TIME_WAIT_S_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property($onehot0({ CLOSED_S, CLOSE_WAIT_S, CLOSING_S, ESTABLISHED_S, FIN_WAIT_1_S, FIN_WAIT_2_S, LAST_ACK_S, LISTEN_S, SYN_RCVD_S, SYN_SENT_S, TIME_WAIT_S }));
end


endmodule
