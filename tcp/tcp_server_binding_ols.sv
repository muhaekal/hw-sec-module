// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 11.04.2025 at 09:25                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


bind tcp_server fv_tcp_server_m fv_tcp_server(
  .rst(tcp_server.rst),
  .clk(tcp_server.clk),

  // Ports
  .ACK_in(tcp_server.ACK_in),

  .ack_number_in(tcp_server.ack_number_in),

  .ACK_port_vld(tcp_server.ACK_port_vld),
  .ACK_port_rdy(tcp_server.ACK_port_rdy),
  .ACK_port(tcp_server.ACK_port),

  .ACK_port_2_vld(tcp_server.ACK_port_2_vld),
  .ACK_port_2_rdy(tcp_server.ACK_port_2_rdy),
  .ACK_port_2(tcp_server.ACK_port_2),

  .ACK_port_3_vld(tcp_server.ACK_port_3_vld),
  .ACK_port_3_rdy(tcp_server.ACK_port_3_rdy),
  .ACK_port_3(tcp_server.ACK_port_3),

  .ctl_loc_port_in(tcp_server.ctl_loc_port_in),

  .dst_port_in(tcp_server.dst_port_in),

  .FIN_in(tcp_server.FIN_in),

  .force_dcn_in(tcp_server.force_dcn_in),

  .last_ack_in(tcp_server.last_ack_in),

  .listen_in(tcp_server.listen_in),

  .pkt_stop_in(tcp_server.pkt_stop_in),

  .PSH_in(tcp_server.PSH_in),

  .RST_in(tcp_server.RST_in),

  .seq_number_in(tcp_server.seq_number_in),

  .src_port_in(tcp_server.src_port_in),

  .SYN_in(tcp_server.SYN_in),

  .SYN_port_vld(tcp_server.SYN_port_vld),
  .SYN_port_rdy(tcp_server.SYN_port_rdy),
  .SYN_port(tcp_server.SYN_port),

  .SYN_port_2_vld(tcp_server.SYN_port_2_vld),
  .SYN_port_2_rdy(tcp_server.SYN_port_2_rdy),
  .SYN_port_2(tcp_server.SYN_port_2),

  .tx_ctl_loc_seq_in(tcp_server.tx_ctl_loc_seq_in),

  .tx_done_in(tcp_server.tx_done_in),

  .tx_eng_acc_in(tcp_server.tx_eng_acc_in),

  .ack_number_out(tcp_server.ack_number_out),

  .ACK_out(tcp_server.ACK_out),

  .dst_port_out(tcp_server.dst_port_out),

  .FIN_out(tcp_server.FIN_out),

  .RST_out(tcp_server.RST_out),

  .seq_number_out(tcp_server.seq_number_out),

  .src_port_out(tcp_server.src_port_out),

  .SYN_out(tcp_server.SYN_out),

  // Registers
  .close_reset(tcp_server.close_reset),
  .local_ack(tcp_server.tcp_server_computational_inst.local_ack),
  .local_port(tcp_server.local_port),
  .local_seq(tcp_server.tcp_server_computational_inst.local_seq),
  .remote_port(tcp_server.remote_port),

  // States
  .ABSTRACT_S(tcp_server.tcp_server_control_inst.current_state == 7),
  .CLOSED_S(tcp_server.tcp_server_control_inst.current_state == 0),
  .ESTABLISHED_1_S(tcp_server.tcp_server_control_inst.current_state == 5),
  .ESTABLISHED_S(tcp_server.tcp_server_control_inst.current_state == 4),
  .FLUSH_S(tcp_server.tcp_server_control_inst.current_state == 6),
  .LISTEN_S(tcp_server.tcp_server_control_inst.current_state == 1),
  .RST_RCVD_S(tcp_server.tcp_server_control_inst.current_state == 8),
  .SYN_RCVD_1_S(tcp_server.tcp_server_control_inst.current_state == 3),
  .SYN_RCVD_S(tcp_server.tcp_server_control_inst.current_state == 2)
);
