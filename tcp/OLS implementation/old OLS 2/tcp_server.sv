// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.04.2025 at 11:36                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import global_package::*;
import tcp_server_operations::*;


module tcp_server (
  input  logic                 rst,
  input  logic                 clk,
  input  logic                 ACK_in,
  output logic                 ACK_out,
  input  logic                 ACK_port,
  input  logic                 ACK_port_vld,
  output logic                 ACK_port_rdy,
  input  logic                 ACK_port_2,
  input  logic                 ACK_port_2_vld,
  output logic                 ACK_port_2_rdy,
  input  logic                 ACK_port_3,
  input  logic                 ACK_port_3_vld,
  output logic                 ACK_port_3_rdy,
  input  logic                 FIN_in,
  output logic                 FIN_out,
  input  logic                 PSH_in,
  input  logic                 RST_in,
  output logic                 RST_out,
  input  logic                 SYN_in,
  output logic                 SYN_out,
  input  logic                 SYN_port,
  input  logic                 SYN_port_vld,
  output logic                 SYN_port_rdy,
  input  logic                 SYN_port_2,
  input  logic                 SYN_port_2_vld,
  output logic                 SYN_port_2_rdy,
  input  logic unsigned [31:0] ack_number_in,
  output logic unsigned [31:0] ack_number_out,
  input  logic unsigned [15:0] ctl_loc_port_in,
  input  logic unsigned [15:0] dst_port_in,
  output logic unsigned [15:0] dst_port_out,
  input  logic                 force_dcn_in,
  input  logic unsigned [31:0] last_ack_in,
  input  logic                 listen_in,
  input  logic unsigned [31:0] pkt_stop_in,
  input  logic unsigned [31:0] seq_number_in,
  output logic unsigned [31:0] seq_number_out,
  input  logic unsigned [15:0] src_port_in,
  output logic unsigned [15:0] src_port_out,
  input  logic unsigned [31:0] tx_ctl_loc_seq_in,
  input  logic                 tx_done_in,
  input  logic                 tx_eng_acc_in,
  input  logic                 abstract_port_vld
);

  //logic                   abstract_port_vld;
  logic                   close_reset;
  logic unsigned [15:0]   local_port;
  logic unsigned [15:0]   remote_port;
  tcp_server_operations_t operation;

  tcp_server_control tcp_server_control_inst (
    .rst              (rst),
    .clk              (clk),
    .FIN_in           (FIN_in),
    .RST_in           (RST_in),
    .dst_port_in      (dst_port_in),
    .force_dcn_in     (force_dcn_in),
    .listen_in        (listen_in),
    .src_port_in      (src_port_in),
    .tx_done_in       (tx_done_in),
    .ACK_port_2_vld   (ACK_port_2_vld),
    .ACK_port_3_vld   (ACK_port_3_vld),
    .SYN_port_vld     (SYN_port_vld),
    .abstract_port_vld(abstract_port_vld),
    .close_reset      (close_reset),
    .local_port       (local_port),
    .remote_port      (remote_port),
    .operation        (operation)
  );

  tcp_server_computational tcp_server_computational_inst (
    .rst                  (rst),
    .clk                  (clk),
    .ACK_in               (ACK_in),
    .ACK_out              (ACK_out),
    .ACK_port             (ACK_port),
    .ACK_port_rdy         (ACK_port_rdy),
    .ACK_port_2           (ACK_port_2),
    .ACK_port_2_rdy       (ACK_port_2_rdy),
    .ACK_port_3           (ACK_port_3),
    .ACK_port_3_rdy       (ACK_port_3_rdy),
    .FIN_in               (FIN_in),
    .FIN_out              (FIN_out),
    .PSH_in               (PSH_in),
    .RST_in               (RST_in),
    .RST_out              (RST_out),
    .SYN_in               (SYN_in),
    .SYN_out              (SYN_out),
    .SYN_port             (SYN_port),
    .SYN_port_rdy         (SYN_port_rdy),
    .SYN_port_2           (SYN_port_2),
    .SYN_port_2_rdy       (SYN_port_2_rdy),
    .ack_number_in        (ack_number_in),
    .ack_number_out       (ack_number_out),
    .ctl_loc_port_in      (ctl_loc_port_in),
    .dst_port_in          (dst_port_in),
    .dst_port_out         (dst_port_out),
    .force_dcn_in         (force_dcn_in),
    .last_ack_in          (last_ack_in),
    .listen_in            (listen_in),
    .pkt_stop_in          (pkt_stop_in),
    .seq_number_in        (seq_number_in),
    .seq_number_out       (seq_number_out),
    .src_port_in          (src_port_in),
    .src_port_out         (src_port_out),
    .tx_ctl_loc_seq_in    (tx_ctl_loc_seq_in),
    .tx_done_in           (tx_done_in),
    .tx_eng_acc_in        (tx_eng_acc_in),
    //.abstract_port_vld_out(abstract_port_vld),
    .close_reset_out      (close_reset),
    .local_port_out       (local_port),
    .remote_port_out      (remote_port),
    .operation            (operation)
  );

endmodule
