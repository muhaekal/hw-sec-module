property no_connect_p;
   tcp_vlg_engine.ctl.connect == 1'd0 && //tcp is tcp_server
   !tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.rst && // to not enable rst_rec in EtoE
   $stable(tcp_vlg_engine.ctl.loc_port) && //stable value of local_port_number
   $stable(tcp_vlg_engine.rx.meta.tcp_hdr.dst_port) &&
   tcp_vlg_engine.rx.meta.tcp_opt.tcp_opt_pres.wnd_pres == 1'd0 //no window option assumption
   ;
endproperty
no_connect_a: assume property (disable iff(rst) no_connect_p);


property syn_val_p; //valid is 1 when flags are received
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.syn ||
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack ||
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.fin
|->
tcp_vlg_engine.rx.meta.val == 1'd1
;
endproperty
syn_val_a: assume property (disable iff(rst) syn_val_p);

/*property stable_fin_p; //if close_active, no fin generated to not change the close condition.
ESTABLISHED_1_S &&
close_active
|->
!tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.fin
;
endproperty
//stable_fin_a: assume property (disable iff(rst) stable_fin_p);

property stable_fin_2_p; //if close_passive, no close active generated
ESTABLISHED_1_S &&
close_passive
|->
!close
;
endproperty
//stable_fin_2_a: assume property (disable iff(rst) stable_fin_2_p);*/


property flushed_p;
tcp_vlg_engine.tx_ctl.flushed
;
endproperty
flushed_a: assume property (disable iff(rst) flushed_p); //for E to CW AIP

//new model 

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

property stable_close_p;
tcp_vlg_engine.fsm == 10
|->
$stable(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.rst) &&
$stable(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.fin) &&
$stable(tcp_vlg_engine.ctl.listen) &&
$stable(tcp_vlg_engine.tx_ctl.force_dcn)
;
endproperty
//stable_close_a: assume property (stable_close_p);  //during established state, close inputs should be stable

property no_rst_rec_p;
!tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.rst; // assume no rst_rec from client
endproperty
//no_rst_rec_a: assume property (disable iff(rst) no_rst_rec_p);

property stable_seq_number_in_p;
   //SYN_RCVD_1_S &&
   //!tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack
   //|->
   $stable(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_seq_num); 
   //because seq_num input in syn rcvd1 to syn rcvd1 is not stable. 
   //but if i add this assumption, syn rcvd1 to established transition becomes unreachable
endproperty
//stable_seq_number_in_a: assume property (disable iff(rst) stable_seq_number_in_p);

property listen_p;
!CLOSED_S
|->
tcp_vlg_engine.ctl.listen == 1'd1
; //to not enable usr_dcn during established to established transition.
endproperty
//listen_a: assume property (disable iff(rst) listen_p);

property flushed_p;
tcp_vlg_engine.tx_ctl.flushed; //to enable flushed input for established to abstract transition
endproperty
//flushed_a: assume property (disable iff(rst) flushed_p);

property acc_p;
tcp_vlg_engine.fsm == 14 //dcn_send_ack_s
|->
tcp_vlg_engine.tx_eng.acc; //to enable transition from dcn_send_ack to dcn_ack_sent
endproperty
//acc_a: assume property (disable iff(rst) acc_p);

property fin_acc_p;
tcp_vlg_engine.fsm == 12 //dcn_send_fin_s
|->
tcp_vlg_engine.tx_eng.acc; //to enable transition from dcn_send_fin to dcn_fin_sent
endproperty
//fin_acc_a: assume property (disable iff(rst) fin_acc_p);

property a;
tcp_vlg_engine.fsm == 12;
endproperty
//cover_a: cover property (disable iff(rst) a);

property last_ack_p;
tcp_vlg_engine.fsm == 15 //dcn_ack_sent_s
|->
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack; //to enable transition from dcn_ack_sent to closed_s
endproperty
//last_ack_a: assume property (disable iff(rst) last_ack_p);

property fin_sent_p;
tcp_vlg_engine.fsm == 13 //dcn_fin_sent_s
|->
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.ack &&
tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.fin; //to enable transition from dcn_fin_sent to send_ack_s
endproperty
//fin_sent_a: assume property (disable iff(rst) fin_sent_p);


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

property stable_close_p;
//tcp_vlg_engine.fsm == 10
ESTABLISHED_1_S
|->
$stable(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.rst) &&
$stable(tcp_vlg_engine.rx.meta.tcp_hdr.tcp_flags.fin) &&
$stable(tcp_vlg_engine.ctl.listen) &&
$stable(tcp_vlg_engine.tx_ctl.force_dcn)
;
endproperty
//stable_close_a: assume property (stable_close_p);