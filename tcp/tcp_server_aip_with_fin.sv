// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 29.04.2025 at 10:34                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import tcp_server_pkg::*;


module fv_tcp_server_m(
  input logic rst,
  input logic clk,

  // Ports
  input logic unsigned [15:0] src_port_in,

  input logic unsigned [15:0] dst_port_in,

  input logic unsigned [15:0] ctl_loc_port_in,

  input logic unsigned [31:0] seq_number_in,

  input logic unsigned [31:0] ack_number_in,

  input logic unsigned [31:0] pkt_stop_in,

  input logic SYN_in,

  input logic ACK_in,

  input logic FIN_in,

  input logic PSH_in,

  input logic RST_in,

  input logic listen_in,

  input logic force_dcn_in,

  input logic ACK_port_vld,
  input logic ACK_port_rdy,
  input logic ACK_port,

  input logic ACK_port_2_vld,
  input logic ACK_port_2_rdy,
  input logic ACK_port_2,

  input logic ACK_port_3_vld,
  input logic ACK_port_3_rdy,
  input logic ACK_port_3,

  input logic SYN_port_vld,
  input logic SYN_port_rdy,
  input logic SYN_port,

  input logic SYN_port_2_vld,
  input logic SYN_port_2_rdy,
  input logic SYN_port_2,

  input logic unsigned [31:0] tx_ctl_loc_seq_in,

  input logic tx_done_in,

  input logic tx_eng_acc_in,

  input logic unsigned [31:0] last_ack_in,

  input logic unsigned [15:0] src_port_out,

  input logic unsigned [15:0] dst_port_out,

  input logic unsigned [31:0] seq_number_out,

  input logic unsigned [31:0] ack_number_out,

  input logic SYN_out,

  input logic ACK_out,

  input logic FIN_out,

  input logic RST_out,

  // Registers
  input logic abstract_port_vld,
  input logic close_reset,
  input logic dcn_send_ack,
  input logic dcn_send_fin,
  input logic unsigned [31:0] local_ack,
  input logic unsigned [15:0] local_port,
  input logic unsigned [31:0] local_seq,
  input logic unsigned [15:0] remote_port,

  // States
  input logic CLOSED_S,
  input logic LISTEN_S,
  input logic SYN_RCVD_S,
  input logic SYN_RCVD_1_S,
  input logic ESTABLISHED_S,
  input logic ESTABLISHED_1_S,
  input logic FLUSH_S,
  input logic ABSTRACT_S,
  input logic RST_RCVD_S,
  input logic undriven_state
);


default clocking default_clk @(posedge clk); endclocking


sequence reset_sequence;
  rst ##1 !rst;
endsequence


property run_reset_p;
  reset_sequence |->
  CLOSED_S &&
  ACK_out == 0 &&
  FIN_out == 0 &&
  RST_out == 0 &&
  SYN_out == 0 &&
  ack_number_out == 0 &&
  dst_port_out == 16'd0 &&
  local_ack == 0 &&
  local_port == 16'd0 &&
  local_seq == 0 &&
  remote_port == 16'd0 &&
  seq_number_out == 0 &&
  src_port_out == 16'd0;
endproperty
run_reset_a: assert property (run_reset_p);

property syn_val_p; //valid is 1 when flags are received
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.syn || //to activate syn_rec
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack ||
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.fin ||
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.rst
|->
tcp_vlg_engine.rx.meta.val == 1'd1
;
endproperty
syn_val_a: assume property (disable iff(rst) syn_val_p);

property no_connect_p;
   tcp_vlg_engine.ctl.connect == 1'd0; // model is tcp server, so connect is always 0 (client = 0)
endproperty
no_connect_a: assume property (disable iff(rst) no_connect_p);

property no_window_p;
   tcp_vlg_engine.rx.meta.tcp_opt.tcp_opt_pres.wnd_pres == 1'd0; //no window option assumption, so scl state can be skipped.
endproperty
no_window_a: assume property (disable iff(rst) no_window_p);



property run_ABSTRACT_S_to_ABSTRACT_S_p;
  ABSTRACT_S &&
  dcn_send_ack &&
  tx_eng_acc_in
|->
  ##1 ($stable(RST_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ABSTRACT_S &&
  ACK_out == 1 &&
  FIN_out == 0 &&
  SYN_out == 0 &&
  ack_number_out == 32'((64'd1 + ({ 'h0, $past(local_ack, 1)} ))) &&
  local_ack == (1 + $past(local_ack, 1)) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port) &&
  seq_number_out == $past(local_seq, 1);
endproperty
run_ABSTRACT_S_to_ABSTRACT_S_a: assert property (disable iff(rst) run_ABSTRACT_S_to_ABSTRACT_S_p);


property run_ABSTRACT_S_to_ABSTRACT_S_1_p;
  ABSTRACT_S &&
  dcn_send_ack &&
  !tx_eng_acc_in
|->
  ##1 ($stable(RST_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ABSTRACT_S &&
  ACK_out == 1 &&
  FIN_out == 0 &&
  SYN_out == 0 &&
  ack_number_out == 32'((64'd1 + ({ 'h0, $past(local_ack, 1)} ))) &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port) &&
  seq_number_out == $past(local_seq, 1);
endproperty
run_ABSTRACT_S_to_ABSTRACT_S_1_a: assert property (disable iff(rst) run_ABSTRACT_S_to_ABSTRACT_S_1_p);


property run_ABSTRACT_S_to_ABSTRACT_S_2_p;
  ABSTRACT_S &&
  !dcn_send_ack &&
  dcn_send_fin
|->
  ##1 ($stable(RST_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ABSTRACT_S &&
  ACK_out == 1 &&
  FIN_out == 1 &&
  SYN_out == 0 &&
  ack_number_out == $past(local_ack, 1) &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port) &&
  seq_number_out == $past(local_seq, 1);
endproperty
run_ABSTRACT_S_to_ABSTRACT_S_2_a: assert property (disable iff(rst) run_ABSTRACT_S_to_ABSTRACT_S_2_p);


property run_ABSTRACT_S_to_ABSTRACT_S_3_p;
  ABSTRACT_S &&
  !dcn_send_ack &&
  !dcn_send_fin &&
  !abstract_port_vld
|->
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ABSTRACT_S &&
  ACK_out == 1 &&
  SYN_out == 0 &&
  ack_number_out == $past(local_ack, 1) &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port) &&
  seq_number_out == $past(local_seq, 1);
endproperty
run_ABSTRACT_S_to_ABSTRACT_S_3_a: assert property (disable iff(rst) run_ABSTRACT_S_to_ABSTRACT_S_3_p);


property run_ABSTRACT_S_to_CLOSED_S_p;
  ABSTRACT_S &&
  !dcn_send_ack &&
  !dcn_send_fin &&
  abstract_port_vld
|->
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  CLOSED_S &&
  ACK_out == 1 &&
  SYN_out == 0 &&
  ack_number_out == $past(local_ack, 1) &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port) &&
  seq_number_out == $past(local_seq, 1);
endproperty
run_ABSTRACT_S_to_CLOSED_S_a: assert property (disable iff(rst) run_ABSTRACT_S_to_CLOSED_S_p);


property run_CLOSED_S_to_CLOSED_S_p;
  CLOSED_S &&
  !listen_in
|->
  ##1
  CLOSED_S &&
  ACK_out == 0 &&
  FIN_out == 0 &&
  RST_out == 0 &&
  SYN_out == 0 &&
  ack_number_out == 0 &&
  dst_port_out == 16'd0 &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port) &&
  seq_number_out == 0 &&
  src_port_out == 16'd0;
endproperty
run_CLOSED_S_to_CLOSED_S_a: assert property (disable iff(rst) run_CLOSED_S_to_CLOSED_S_p);


property run_CLOSED_S_to_LISTEN_S_p;
  CLOSED_S &&
  listen_in
|->
  ##1
  LISTEN_S &&
  ACK_out == 0 &&
  FIN_out == 0 &&
  RST_out == 0 &&
  SYN_out == 0 &&
  ack_number_out == 0 &&
  dst_port_out == 16'd0 &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port) &&
  seq_number_out == 0 &&
  src_port_out == 16'd0;
endproperty
run_CLOSED_S_to_LISTEN_S_a: assert property (disable iff(rst) run_CLOSED_S_to_LISTEN_S_p);


property run_ESTABLISHED_1_S_to_FLUSH_S_p;
  ESTABLISHED_1_S &&
  tx_done_in
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  FLUSH_S &&
  local_ack == $past(last_ack_in, 1) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_1_S_to_FLUSH_S_a: assert property (disable iff(rst) run_ESTABLISHED_1_S_to_FLUSH_S_p);


property run_ESTABLISHED_1_S_to_FLUSH_S_1_p;
  ESTABLISHED_1_S &&
  !tx_done_in
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  FLUSH_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_1_S_to_FLUSH_S_1_a: assert property (disable iff(rst) run_ESTABLISHED_1_S_to_FLUSH_S_1_p);


property run_ESTABLISHED_S_to_ESTABLISHED_1_S_p;
  ESTABLISHED_S &&
  tx_done_in &&
  (!listen_in || force_dcn_in)
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ESTABLISHED_1_S &&
  local_ack == $past(last_ack_in, 1) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_S_to_ESTABLISHED_1_S_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_ESTABLISHED_1_S_p);


property run_ESTABLISHED_S_to_ESTABLISHED_1_S_1_p;
  ESTABLISHED_S &&
  tx_done_in &&
  listen_in &&
  !force_dcn_in &&
  FIN_in &&
  (src_port_in == remote_port) &&
  (dst_port_in == local_port)
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ESTABLISHED_1_S &&
  local_ack == $past(last_ack_in, 1) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_S_to_ESTABLISHED_1_S_1_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_ESTABLISHED_1_S_1_p);


property run_ESTABLISHED_S_to_ESTABLISHED_1_S_2_p;
  ESTABLISHED_S &&
  tx_done_in &&
  listen_in &&
  !force_dcn_in &&
  !((FIN_in && (src_port_in == remote_port)) && (dst_port_in == local_port)) &&
  RST_in &&
  (src_port_in == remote_port) &&
  (dst_port_in == local_port)
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ESTABLISHED_1_S &&
  local_ack == $past(last_ack_in, 1) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_S_to_ESTABLISHED_1_S_2_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_ESTABLISHED_1_S_2_p);


property run_ESTABLISHED_S_to_ESTABLISHED_1_S_3_p;
  ESTABLISHED_S &&
  !tx_done_in &&
  (!listen_in || force_dcn_in)
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ESTABLISHED_1_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_S_to_ESTABLISHED_1_S_3_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_ESTABLISHED_1_S_3_p);


property run_ESTABLISHED_S_to_ESTABLISHED_1_S_4_p;
  ESTABLISHED_S &&
  !tx_done_in &&
  listen_in &&
  !force_dcn_in &&
  FIN_in &&
  (src_port_in == remote_port) &&
  (dst_port_in == local_port)
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ESTABLISHED_1_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_S_to_ESTABLISHED_1_S_4_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_ESTABLISHED_1_S_4_p);


property run_ESTABLISHED_S_to_ESTABLISHED_1_S_5_p;
  ESTABLISHED_S &&
  !tx_done_in &&
  listen_in &&
  !force_dcn_in &&
  !((FIN_in && (src_port_in == remote_port)) && (dst_port_in == local_port)) &&
  RST_in &&
  (src_port_in == remote_port) &&
  (dst_port_in == local_port)
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ESTABLISHED_1_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_S_to_ESTABLISHED_1_S_5_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_ESTABLISHED_1_S_5_p);


property run_ESTABLISHED_S_to_ESTABLISHED_S_p;
  ESTABLISHED_S &&
  tx_done_in &&
  listen_in &&
  !force_dcn_in &&
  !((FIN_in && (src_port_in == remote_port)) && (dst_port_in == local_port)) &&
  !((RST_in && (src_port_in == remote_port)) && (dst_port_in == local_port))
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ESTABLISHED_S &&
  local_ack == $past(last_ack_in, 1) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_S_to_ESTABLISHED_S_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_ESTABLISHED_S_p);


property run_ESTABLISHED_S_to_ESTABLISHED_S_1_p;
  ESTABLISHED_S &&
  !tx_done_in &&
  listen_in &&
  !force_dcn_in &&
  !((FIN_in && (src_port_in == remote_port)) && (dst_port_in == local_port)) &&
  !((RST_in && (src_port_in == remote_port)) && (dst_port_in == local_port))
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ESTABLISHED_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  local_seq == $past(tx_ctl_loc_seq_in, 1) &&
  $stable(remote_port);
endproperty
run_ESTABLISHED_S_to_ESTABLISHED_S_1_a: assert property (disable iff(rst) run_ESTABLISHED_S_to_ESTABLISHED_S_1_p);


property run_FLUSH_S_to_ABSTRACT_S_p;
  FLUSH_S &&
  ACK_port_3_vld &&
  !close_reset
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ABSTRACT_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port);
endproperty
run_FLUSH_S_to_ABSTRACT_S_a: assert property (disable iff(rst) run_FLUSH_S_to_ABSTRACT_S_p);


property run_FLUSH_S_to_RST_RCVD_S_p;
  FLUSH_S &&
  ACK_port_3_vld &&
  close_reset
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  RST_RCVD_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port);
endproperty
run_FLUSH_S_to_RST_RCVD_S_a: assert property (disable iff(rst) run_FLUSH_S_to_RST_RCVD_S_p);


property run_LISTEN_S_to_SYN_RCVD_S_p;
  LISTEN_S &&
  SYN_port_vld
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  SYN_RCVD_S &&
  local_ack == 32'((64'd1 + $past(seq_number_in, 1))) &&
  local_port == $past(ctl_loc_port_in, 1) &&
  local_seq == 'h7D0 &&
  remote_port == $past(src_port_in, 1);
endproperty
run_LISTEN_S_to_SYN_RCVD_S_a: assert property (disable iff(rst) run_LISTEN_S_to_SYN_RCVD_S_p);


property run_RST_RCVD_S_to_CLOSED_S_p;
  RST_RCVD_S
|->
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  CLOSED_S &&
  ACK_out == 1 &&
  FIN_out == 0 &&
  RST_out == 1 &&
  SYN_out == 0 &&
  ack_number_out == $past(local_ack, 1) &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port) &&
  seq_number_out == $past(local_seq, 1);
endproperty
run_RST_RCVD_S_to_CLOSED_S_a: assert property (disable iff(rst) run_RST_RCVD_S_to_CLOSED_S_p);


property run_SYN_RCVD_1_S_to_ESTABLISHED_S_p;
  SYN_RCVD_1_S &&
  ACK_port_2_vld
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  ESTABLISHED_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  local_seq == (1 + $past(local_seq, 1)) &&
  $stable(remote_port);
endproperty
run_SYN_RCVD_1_S_to_ESTABLISHED_S_a: assert property (disable iff(rst) run_SYN_RCVD_1_S_to_ESTABLISHED_S_p);


property run_SYN_RCVD_S_to_SYN_RCVD_1_S_p;
  SYN_RCVD_S
|->
  ##1
  SYN_RCVD_1_S &&
  ACK_out == 1 &&
  FIN_out == 0 &&
  RST_out == 0 &&
  SYN_out == 1 &&
  ack_number_out == $past(local_ack, 1) &&
  dst_port_out == $past(remote_port, 1) &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port) &&
  seq_number_out == $past(local_seq, 1) &&
  src_port_out == $past(local_port, 1);
endproperty
run_SYN_RCVD_S_to_SYN_RCVD_1_S_a: assert property (disable iff(rst) run_SYN_RCVD_S_to_SYN_RCVD_1_S_p);


property run_FLUSH_S_wait_p;
  FLUSH_S &&
  !ACK_port_3_vld
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  FLUSH_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port);
endproperty
run_FLUSH_S_wait_a: assert property (disable iff(rst) run_FLUSH_S_wait_p);


property run_LISTEN_S_wait_p;
  LISTEN_S &&
  !SYN_port_vld
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  LISTEN_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port);
endproperty
run_LISTEN_S_wait_a: assert property (disable iff(rst) run_LISTEN_S_wait_p);


property run_SYN_RCVD_1_S_wait_p;
  SYN_RCVD_1_S &&
  !ACK_port_2_vld
|->
  ##1 ($stable(ACK_out)) and
  ##1 ($stable(FIN_out)) and
  ##1 ($stable(RST_out)) and
  ##1 ($stable(SYN_out)) and
  ##1 ($stable(ack_number_out)) and
  ##1 ($stable(dst_port_out)) and
  ##1 ($stable(seq_number_out)) and
  ##1 ($stable(src_port_out)) and
  ##1
  SYN_RCVD_1_S &&
  $stable(local_ack) &&
  $stable(local_port) &&
  $stable(local_seq) &&
  $stable(remote_port);
endproperty
run_SYN_RCVD_1_S_wait_a: assert property (disable iff(rst) run_SYN_RCVD_1_S_wait_p);

/*
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


property run_SYN_RCVD_S_eventually_left_p;
  SYN_RCVD_S
|->
  s_eventually(!SYN_RCVD_S);
endproperty
run_SYN_RCVD_S_eventually_left_a: assert property (disable iff(rst) run_SYN_RCVD_S_eventually_left_p);


property run_SYN_RCVD_1_S_eventually_left_p;
  SYN_RCVD_1_S
|->
  s_eventually(!SYN_RCVD_1_S);
endproperty
run_SYN_RCVD_1_S_eventually_left_a: assert property (disable iff(rst) run_SYN_RCVD_1_S_eventually_left_p);


property run_ESTABLISHED_S_eventually_left_p;
  ESTABLISHED_S
|->
  s_eventually(!ESTABLISHED_S);
endproperty
run_ESTABLISHED_S_eventually_left_a: assert property (disable iff(rst) run_ESTABLISHED_S_eventually_left_p);


property run_ESTABLISHED_1_S_eventually_left_p;
  ESTABLISHED_1_S
|->
  s_eventually(!ESTABLISHED_1_S);
endproperty
run_ESTABLISHED_1_S_eventually_left_a: assert property (disable iff(rst) run_ESTABLISHED_1_S_eventually_left_p);


property run_FLUSH_S_eventually_left_p;
  FLUSH_S
|->
  s_eventually(!FLUSH_S);
endproperty
run_FLUSH_S_eventually_left_a: assert property (disable iff(rst) run_FLUSH_S_eventually_left_p);


property run_ABSTRACT_S_eventually_left_p;
  ABSTRACT_S
|->
  s_eventually(!ABSTRACT_S);
endproperty
run_ABSTRACT_S_eventually_left_a: assert property (disable iff(rst) run_ABSTRACT_S_eventually_left_p);


property run_RST_RCVD_S_eventually_left_p;
  RST_RCVD_S
|->
  s_eventually(!RST_RCVD_S);
endproperty
run_RST_RCVD_S_eventually_left_a: assert property (disable iff(rst) run_RST_RCVD_S_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property($onehot0({ ABSTRACT_S, CLOSED_S, ESTABLISHED_1_S, ESTABLISHED_S, FLUSH_S, LISTEN_S, RST_RCVD_S, SYN_RCVD_1_S, SYN_RCVD_S }));
end
*/

endmodule
