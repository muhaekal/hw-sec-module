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
  output logic                 match,
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

assign match = tcp_server.ACK_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.ack &&
               tcp_server.SYN_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.syn &&
               tcp_server.RST_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_flags.rst &&
               tcp_server.seq_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_seq_num &&
               tcp_server.ack_number_out == dut_inst.tx_eng.meta.tcp_hdr.tcp_ack_num &&
               tcp_server.src_port_out == dut_inst.tx_eng.meta.tcp_hdr.src_port &&
               tcp_server.dst_port_out == dut_inst.tx_eng.meta.tcp_hdr.dst_port;


endmodule