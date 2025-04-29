// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.04.2025 at 15:56                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


bind tcp_vlg_engine fv_tcp_server_m fv_tcp_server(
  .rst(tcp_vlg_engine.rst),
  .clk(tcp_vlg_engine.clk),

  // Ports
  .ACK_in(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack),

  .ack_number_in(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_ack_num),

  .ACK_port_vld((tcp_vlg_engine.fsm == dcn_ack_sent_s) && tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack && (tcp_vlg_engine.rx.meta.tcp_hdr.src_port == tcp_vlg_engine.tcb.rem_port) && (tcp_vlg_engine.rx.meta.tcp_hdr.dst_port == tcp_vlg_engine.tcb.loc_port)),
  .ACK_port_rdy(1'b1),
  .ACK_port(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack),

  .ACK_port_2_vld(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack && (tcp_vlg_engine.rx.meta.tcp_hdr.tcp_seq_num == tcp_vlg_engine.tcb.rem_seq + 1) && (tcp_vlg_engine.rx.meta.tcp_hdr.src_port == tcp_vlg_engine.tcb.rem_port) && (tcp_vlg_engine.rx.meta.tcp_hdr.dst_port == tcp_vlg_engine.tcb.loc_port)),
  .ACK_port_2_rdy(1'b1),
  .ACK_port_2(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack),

  .ACK_port_3_vld(tcp_vlg_engine.tx_ctl.flushed),
  .ACK_port_3_rdy(1'b1),
  .ACK_port_3(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack),

  .ctl_loc_port_in(tcp_vlg_engine.ctl.loc_port),

  .dst_port_in(tcp_vlg_engine.rx.meta.tcp_hdr.dst_port),

  .FIN_in(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.fin),

  .force_dcn_in(tcp_vlg_engine.tx_ctl.force_dcn),

  .last_ack_in(tcp_vlg_engine.last_ack),

  .listen_in(tcp_vlg_engine.ctl.listen),

  .pkt_stop_in(tcp_vlg_engine.rx.meta.pkt_stop),

  .PSH_in(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.psh),

  .RST_in(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.rst),

  .seq_number_in(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_seq_num),

  .src_port_in(tcp_vlg_engine.rx.meta.tcp_hdr.src_port),

  .SYN_in(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.syn),

  .SYN_port_vld(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.syn && (tcp_vlg_engine.rx.meta.tcp_hdr.dst_port == tcp_vlg_engine.ctl.loc_port)),
  .SYN_port_rdy(1'b1),
  .SYN_port(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.syn),

  .SYN_port_2_vld(tcp_vlg_engine.ctl.listen),
  .SYN_port_2_rdy(1'b1),
  .SYN_port_2(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.syn),

  .tx_ctl_loc_seq_in(tcp_vlg_engine.tx_ctl.loc_seq),

  .tx_done_in(tcp_vlg_engine.tx.done),

  .tx_eng_acc_in(tcp_vlg_engine.tx_eng.acc),

  .ack_number_out(tcp_vlg_engine.tx_eng.meta.tcp_hdr.tcp_ack_num),

  .ACK_out(tcp_vlg_engine.tx_eng.meta.tcp_hdr.tcp_flags.ack),

  .dst_port_out(tcp_vlg_engine.tx_eng.meta.tcp_hdr.dst_port),

  .FIN_out(tcp_vlg_engine.tx_eng.meta.tcp_hdr.tcp_flags.fin),

  .RST_out(tcp_vlg_engine.tx_eng.meta.tcp_hdr.tcp_flags.rst),

  .seq_number_out(tcp_vlg_engine.tx_eng.meta.tcp_hdr.tcp_seq_num),

  .src_port_out(tcp_vlg_engine.tx_eng.meta.tcp_hdr.src_port),

  .SYN_out(tcp_vlg_engine.tx_eng.meta.tcp_hdr.tcp_flags.syn),

  // Registers
  .abstract_port_vld((tcp_vlg_engine.fsm == dcn_ack_sent_s) && tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack && (tcp_vlg_engine.rx.meta.tcp_hdr.src_port == tcp_vlg_engine.tcb.rem_port) && (tcp_vlg_engine.rx.meta.tcp_hdr.dst_port == tcp_vlg_engine.tcb.loc_port)),
  .close_reset(tcp_vlg_engine.close == close_reset),
  .dcn_send_ack(tcp_vlg_engine.fsm == dcn_send_ack_s),
  .local_ack(tcp_vlg_engine.tcb.loc_ack),
  .local_port(tcp_vlg_engine.tcb.loc_port),
  .local_seq(tcp_vlg_engine.tcb.loc_seq),
  .remote_port(tcp_vlg_engine.tcb.rem_port),

  // States
  .ABSTRACT_S(tcp_vlg_engine.fsm == dcn_ack_sent_s || tcp_vlg_engine.fsm == dcn_send_ack_s ||  tcp_vlg_engine.fsm == dcn_fin_sent_s || tcp_vlg_engine.fsm == dcn_send_fin_s),
  .CLOSED_S(tcp_vlg_engine.fsm == closed_s),
  .ESTABLISHED_1_S((tcp_vlg_engine.fsm == established_s) && (tcp_vlg_engine.close != close_none)),
  .ESTABLISHED_S((tcp_vlg_engine.fsm == established_s) && (tcp_vlg_engine.close == close_none)),
  .FLUSH_S(tcp_vlg_engine.fsm == flush_s),
  .LISTEN_S(tcp_vlg_engine.fsm == listen_s),
  .RST_RCVD_S(tcp_vlg_engine.fsm == dcn_send_rst_s),
  .SYN_RCVD_1_S(tcp_vlg_engine.fsm == con_syn_ack_sent_s),
  .SYN_RCVD_S(tcp_vlg_engine.fsm == con_send_syn_ack_s)
);
