`include "../open_source_design/eth_vlg_pkg.sv"
`include "../open_source_design/eth_vlg_tmr.sv"
`include "../open_source_design/ipv4_vlg_pkg.sv"
`include "../open_source_design/mac_vlg_pkg.sv"
`include "../open_source_design/pnrg.sv"
`include "../open_source_design/tcp_ctl_ifc.sv"
`include "../open_source_design/tcp_ifc.sv"
`include "../open_source_design/tcp_rx_ctl_ifc.sv"
`include "../open_source_design/tcp_tx_ctl_ifc.sv"
`include "../open_source_design/tcp_vlg_engine.sv"
`include "../open_source_design/tcp_vlg_fast_rtx.sv"
`include "../open_source_design/tcp_vlg_ka.sv"
`include "../open_source_design/tcp_vlg_pkg.sv"
`include "../open_source_design/tcp_vlg_tx_arb.sv"
`include "tcp_server.sv"
`include "tcp_server_pkg.sv"
`include "tcp_server_computational.sv"
`include "tcp_server_control.sv"
`include "tcp_server_operations.sv"
`include "global_package.sv"


module VerificationWrapper (
  input  logic                 rst,
  input  logic                 clk,
  tcp_ifc.in_rx                rx,
  tcp_ifc.out_tx               tx,
  tcp_tx_ctl_ifc.out           tx_ctl,
  tcp_rx_ctl_ifc.out           rx_ctl,
  tcp_ctl_ifc.in               ctl

);

//DUT instantiation
tcp_vlg_engine dut_inst (
.rst(rst),
.clk(clk),
.rx(rx),
.tx(tx),
.tx_ctl(tx_ctl),
.rx_ctl(rx_ctl),
.ctl(ctl)
);


//Generated RTL instantiation
tcp_server tcp_server (
  .rst(rst),
  .clk(clk),
  .ACK_in(rx.meta.tcp_hdr.tcp_flags.ack),
  .FIN_in(rx.meta.tcp_hdr.tcp_flags.fin),
  .RST_in(rx.meta.tcp_hdr.tcp_flags.rst),
  .SYN_in(rx.meta.tcp_hdr.tcp_flags.syn),
  .ack_number_in(rx.meta.tcp_hdr.tcp_ack_num),
  .seq_number_in(rx.meta.tcp_hdr.tcp_seq_num),
  .SYN_port_2_vld(ctl.listen),
  .SYN_port_vld(rx.meta.tcp_hdr.tcp_flags.syn && (rx.meta.tcp_hdr.dst_port == ctl.loc_port)),
  .dst_port_in(rx.meta.tcp_hdr.dst_port),
  .src_port_in(rx.meta.tcp_hdr.src_port),
  .ctl_loc_port_in(ctl.loc_port),
  .ACK_port_2_vld(rx.meta.tcp_hdr.tcp_flags.ack && (rx.meta.tcp_hdr.tcp_seq_num == dut_inst.tcb.rem_seq + 1) && (rx.meta.tcp_hdr.src_port == dut_inst.tcb.rem_port) && (rx.meta.tcp_hdr.dst_port == dut_inst.tcb.loc_port)),
  .tx_done_in(tx.done),
  .listen_in(ctl.listen),
  .ACK_port_3_vld(tx_ctl.flushed),
  .tx_ctl_loc_seq_in(tx_ctl.loc_seq),
  .abstract_port_vld((dut_inst.fsm == 15) && rx.meta.tcp_hdr.tcp_flags.ack && (rx.meta.tcp_hdr.src_port == dut_inst.tcb.rem_port) && (rx.meta.tcp_hdr.dst_port == dut_inst.tcb.loc_port)),
  .dcn_send_ack(dut_inst.fsm == 14),
  .tx_eng_acc_in(dut_inst.tx_eng.acc),
  .last_ack_in(dut_inst.last_ack),
  .force_dcn_in(tx_ctl.force_dcn)
);


default clocking default_clk @(posedge clk); endclocking

property syn_val_p; //valid is 1 when flags are received
dut_inst.rx.meta.tcp_hdr.tcp_flags.syn || //to activate syn_rec
dut_inst.rx.meta.tcp_hdr.tcp_flags.ack ||
dut_inst.rx.meta.tcp_hdr.tcp_flags.fin ||
dut_inst.rx.meta.tcp_hdr.tcp_flags.rst
|->
dut_inst.rx.meta.val == 1'd1
;
endproperty
syn_val_a: assume property (disable iff(rst) syn_val_p);

property no_connect_p;
   dut_inst.ctl.connect == 1'd0; // model is tcp server, so connect is always 0 (client = 0)
endproperty
no_connect_a: assume property (disable iff(rst) no_connect_p);

property no_window_p;
   dut_inst.rx.meta.tcp_opt.tcp_opt_pres.wnd_pres == 1'd0; //no window option assumption, so scl state can be skipped.
endproperty
no_window_a: assume property (disable iff(rst) no_window_p);

property stable_close_p; //to have stable input during close condition
dut_inst.fsm == 10
|->
$stable(rx.meta.tcp_hdr.tcp_flags.rst) &&
$stable(rx.meta.tcp_hdr.tcp_flags.fin) &&
$stable(ctl.listen) &&
$stable(tx_ctl.force_dcn)
;
endproperty
stable_close_a: assume property (stable_close_p);

sequence reset_sequence;
  rst ##1 !rst;
endsequence

sequence reset_p_sequence;
  reset_sequence;
endsequence

cover_a: cover property(disable iff(rst) tcp_server.abstract_port_vld);

property reset_p_ec;
  reset_p_sequence
  |->
  tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
  tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
  tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
  tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
  tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
  tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
  tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port; 
endproperty
reset_a_ec: assert property (reset_p_ec);

sequence closed_wait;
  (tcp_server.tcp_server_control_inst.current_state == 0) &&
  (tcp_server.SYN_port_2_vld == 1'd0);
endsequence

property closed_wait_p_ec;
closed_wait 
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
closed_wait_a_ec: assert property (disable iff(rst) closed_wait_p_ec);

sequence closed_to_listen;
  (tcp_server.tcp_server_control_inst.current_state == 0) &&
  (tcp_server.SYN_port_2_vld != 1'd0);
endsequence

property closed_to_listen_p_ec;
closed_to_listen 
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
closed_to_listen_a_ec: assert property (disable iff(rst) closed_to_listen_p_ec);

sequence listen_wait;
  (tcp_server.tcp_server_control_inst.current_state == 1) &&
  (tcp_server.SYN_port_vld == 1'd0);
endsequence

property listen_wait_p_ec;
listen_wait 
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
listen_wait_a_ec: assert property (disable iff(rst) listen_wait_p_ec);

sequence listen_to_syn_rcvd;
  (tcp_server.tcp_server_control_inst.current_state == 1) &&
  (tcp_server.SYN_port_vld != 1'd0);
endsequence

property listen_to_syn_rcvd_p_ec;
listen_to_syn_rcvd
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
listen_to_syn_rcvd_a_ec: assert property (disable iff(rst) listen_to_syn_rcvd_p_ec);

property syn_rcvd_to_syn_rcvd_1_p_ec;
(tcp_server.tcp_server_control_inst.current_state == 2)
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
syn_rcvd_to_syn_rcvd_1_a_ec: assert property (disable iff(rst) syn_rcvd_to_syn_rcvd_1_p_ec);

sequence syn_rcvd_1_wait;
  (tcp_server.tcp_server_control_inst.current_state == 3) &&
  (tcp_server.ACK_port_2_vld == 1'd0);
endsequence

property syn_rcvd_1_wait_p_ec;
syn_rcvd_1_wait 
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
syn_rcvd_1_wait_a_ec: assert property (disable iff(rst) syn_rcvd_1_wait_p_ec);

sequence syn_rcvd_1_to_established;
  (tcp_server.tcp_server_control_inst.current_state == 3) &&
  (tcp_server.ACK_port_2_vld != 1'd0);
endsequence

property syn_rcvd_1_to_established_p_ec;
syn_rcvd_1_to_established
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
syn_rcvd_1_to_established_a_ec: assert property (disable iff(rst) syn_rcvd_1_to_established_p_ec);

sequence established_wait;
  (tcp_server.tcp_server_control_inst.current_state == 4) &&
  tcp_server.tx_done_in &&
  tcp_server.listen_in &&
  !tcp_server.force_dcn_in &&
  !((tcp_server.FIN_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port)) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port)) &&
  !((tcp_server.RST_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port)) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port));
endsequence

property established_wait_p_ec;
established_wait
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_wait_a_ec: assert property (disable iff(rst) established_wait_p_ec);

sequence established_wait_1;
  (tcp_server.tcp_server_control_inst.current_state == 4) &&
  !tcp_server.tx_done_in &&
  tcp_server.listen_in &&
  !tcp_server.force_dcn_in &&
  !((tcp_server.FIN_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port)) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port)) &&
  !((tcp_server.RST_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port)) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port));
endsequence

property established_wait_1_p_ec;
established_wait_1
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_wait_1_a_ec: assert property (disable iff(rst) established_wait_1_p_ec);

sequence established_to_established_1;
  (tcp_server.tcp_server_control_inst.current_state == 4) &&
  tcp_server.tx_done_in &&
  (!tcp_server.listen_in || tcp_server.force_dcn_in);
endsequence

property established_to_established_1_p_ec;
established_to_established_1
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_to_established_1_a_ec: assert property (disable iff(rst) established_to_established_1_p_ec);

sequence established_to_established_1_1;
  (tcp_server.tcp_server_control_inst.current_state == 4) &&
  tcp_server.tx_done_in &&
  tcp_server.listen_in && 
  !tcp_server.force_dcn_in &&
  tcp_server.FIN_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port);
endsequence

property established_to_established_1_1_p_ec;
established_to_established_1_1
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_to_established_1_1_a_ec: assert property (disable iff(rst) established_to_established_1_1_p_ec);

sequence established_to_established_1_2;
  (tcp_server.tcp_server_control_inst.current_state == 4) &&
  tcp_server.tx_done_in &&
  tcp_server.listen_in && 
  !tcp_server.force_dcn_in &&
  !(tcp_server.FIN_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port)) &&
  tcp_server.RST_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port);
endsequence

property established_to_established_1_2_p_ec;
established_to_established_1_2
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_to_established_1_2_a_ec: assert property (disable iff(rst) established_to_established_1_2_p_ec);

sequence established_to_established_1_3;
  (tcp_server.tcp_server_control_inst.current_state == 4) &&
  !tcp_server.tx_done_in &&
  (!tcp_server.listen_in || tcp_server.force_dcn_in);
endsequence

property established_to_established_1_3_p_ec;
established_to_established_1_3
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_to_established_1_3_a_ec: assert property (disable iff(rst) established_to_established_1_3_p_ec);

sequence established_to_established_1_4;
  (tcp_server.tcp_server_control_inst.current_state == 4) &&
  !tcp_server.tx_done_in &&
  tcp_server.listen_in && 
  !tcp_server.force_dcn_in &&
  tcp_server.FIN_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port);
endsequence

property established_to_established_1_4_p_ec;
established_to_established_1_4
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_to_established_1_4_a_ec: assert property (disable iff(rst) established_to_established_1_4_p_ec);

sequence established_to_established_1_5;
  (tcp_server.tcp_server_control_inst.current_state == 4) &&
  !tcp_server.tx_done_in &&
  tcp_server.listen_in && 
  !tcp_server.force_dcn_in &&
  !(tcp_server.FIN_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port)) &&
  tcp_server.RST_in && (tcp_server.src_port_in == dut_inst.tcb.rem_port) && (tcp_server.dst_port_in == dut_inst.tcb.loc_port);
endsequence

property established_to_established_1_5_p_ec;
established_to_established_1_5
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_to_established_1_5_a_ec: assert property (disable iff(rst) established_to_established_1_5_p_ec);

sequence established_1_to_flush;
  (tcp_server.tcp_server_control_inst.current_state == 5) &&
  tcp_server.tx_done_in;
endsequence

property established_1_to_flush_p_ec;
established_1_to_flush
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_1_to_flush_a_ec: assert property (disable iff(rst) established_1_to_flush_p_ec);

sequence established_1_to_flush_1;
  (tcp_server.tcp_server_control_inst.current_state == 5) &&
  !tcp_server.tx_done_in;
endsequence

property established_1_to_flush_1_p_ec;
established_1_to_flush_1
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
established_1_to_flush_1_a_ec: assert property (disable iff(rst) established_1_to_flush_1_p_ec);

sequence flush_wait;
  (tcp_server.tcp_server_control_inst.current_state == 6) &&
  !tcp_server.ACK_port_3_vld;
endsequence

property flush_wait_p_ec;
flush_wait
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
flush_wait_a_ec: assert property (disable iff(rst) flush_wait_p_ec);

sequence flush_to_abstract;
  (tcp_server.tcp_server_control_inst.current_state == 6) &&
  tcp_server.ACK_port_3_vld && !tcp_server.close_reset;
endsequence

property flush_to_abstract_p_ec;
flush_to_abstract
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
flush_to_abstract_a_ec: assert property (disable iff(rst) flush_to_abstract_p_ec);

sequence flush_to_rst_rcvd;
  (tcp_server.tcp_server_control_inst.current_state == 6) &&
  tcp_server.ACK_port_3_vld && tcp_server.close_reset;
endsequence

property flush_to_rst_rcvd_p_ec;
flush_to_rst_rcvd
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
flush_to_rst_rcvd_a_ec: assert property (disable iff(rst) flush_to_rst_rcvd_p_ec);

sequence abstract_wait;
  (tcp_server.tcp_server_control_inst.current_state == 7) &&
  tcp_server.dcn_send_ack &&
  tcp_server.tx_eng_acc_in;
endsequence

property abstract_wait_p_ec;
abstract_wait 
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
abstract_wait_a_ec: assert property (disable iff(rst) abstract_wait_p_ec);

sequence abstract_wait_1;
  (tcp_server.tcp_server_control_inst.current_state == 7) &&
  tcp_server.dcn_send_ack &&
  !tcp_server.tx_eng_acc_in;
endsequence

property abstract_wait_1_p_ec;
abstract_wait_1
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
abstract_wait_1_a_ec: assert property (disable iff(rst) abstract_wait_1_p_ec);

sequence abstract_wait_2;
  (tcp_server.tcp_server_control_inst.current_state == 7) &&
  !tcp_server.dcn_send_ack &&
  (tcp_server.abstract_port_vld == 1'd0);
endsequence

property abstract_wait_2_p_ec;
abstract_wait_2
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
abstract_wait_2_a_ec: assert property (disable iff(rst) abstract_wait_2_p_ec);

sequence abstract_to_closed;
  (tcp_server.tcp_server_control_inst.current_state == 7) &&
  !tcp_server.dcn_send_ack &&
  (tcp_server.abstract_port_vld != 1'd0);
endsequence

property abstract_to_closed_p_ec;
abstract_to_closed
|->
##1
tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port
;
endproperty
abstract_to_closed_a_ec: assert property (disable iff(rst) abstract_to_closed_p_ec);

endmodule

