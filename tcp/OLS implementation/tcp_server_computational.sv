// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.04.2025 at 16:09                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import global_package::*;
import tcp_server_operations::*;


module tcp_server_computational (
  input  logic                   rst,
  input  logic                   clk,
  input  logic                   ACK_in,
  output logic                   ACK_out,
  input  logic                   ACK_port,
  output logic                   ACK_port_rdy,
  input  logic                   ACK_port_2,
  output logic                   ACK_port_2_rdy,
  input  logic                   ACK_port_3,
  output logic                   ACK_port_3_rdy,
  input  logic                   FIN_in,
  output logic                   FIN_out,
  input  logic                   PSH_in,
  input  logic                   RST_in,
  output logic                   RST_out,
  input  logic                   SYN_in,
  output logic                   SYN_out,
  input  logic                   SYN_port,
  output logic                   SYN_port_rdy,
  input  logic                   SYN_port_2,
  output logic                   SYN_port_2_rdy,
  input  logic unsigned [31:0]   ack_number_in,
  output logic unsigned [31:0]   ack_number_out,
  input  logic unsigned [15:0]   ctl_loc_port_in,
  input  logic unsigned [15:0]   dst_port_in,
  output logic unsigned [15:0]   dst_port_out,
  input  logic                   force_dcn_in,
  input  logic unsigned [31:0]   last_ack_in,
  input  logic                   listen_in,
  input  logic unsigned [31:0]   pkt_stop_in,
  input  logic unsigned [31:0]   seq_number_in,
  output logic unsigned [31:0]   seq_number_out,
  input  logic unsigned [15:0]   src_port_in,
  output logic unsigned [15:0]   src_port_out,
  input  logic unsigned [31:0]   tx_ctl_loc_seq_in,
  input  logic                   tx_done_in,
  input  logic                   tx_eng_acc_in,
  output logic                   abstract_port_vld_out,
  output logic                   close_reset_out,
  output logic                   dcn_send_ack_out,
  output logic unsigned [15:0]   local_port_out,
  output logic unsigned [15:0]   remote_port_out,
  input  tcp_server_operations_t operation
);

  logic                 abstract_port_vld;
  logic                 close_reset;
  logic                 dcn_send_ack;
  logic unsigned [31:0] local_ack;
  logic unsigned [15:0] local_port;
  logic unsigned [31:0] local_seq;
  logic unsigned [15:0] remote_port;

  always_ff @(posedge clk) begin
    if (rst)
      abstract_port_vld <= 0;
  end

  always_ff @(posedge clk) begin
    if (rst)
      close_reset <= 0;
    else begin
      if (operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1)
        close_reset <= 0;
      else if (operation == tcp_server_op_ESTABLISHED_S_8 || operation == tcp_server_op_ESTABLISHED_S_12)
        close_reset <= 1;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      dcn_send_ack <= 0;
  end

  always_ff @(posedge clk) begin
    if (rst)
      local_ack <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18)
        local_ack <= (1 + local_ack);
      else if (operation == tcp_server_op_ESTABLISHED_1_S_14 || operation == tcp_server_op_ESTABLISHED_S_6 || operation == tcp_server_op_ESTABLISHED_S_7 || operation == tcp_server_op_ESTABLISHED_S_8 || operation == tcp_server_op_ESTABLISHED_S_9)
        local_ack <= last_ack_in;
      else if (operation == tcp_server_op_LISTEN_S_3)
        local_ack <= 32'((64'd1 + seq_number_in));
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      local_port <= 16'd0;
    else begin
      if (operation == tcp_server_op_LISTEN_S_3)
        local_port <= ctl_loc_port_in;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      local_seq <= 0;
    else begin
      if (operation == tcp_server_op_ESTABLISHED_1_S_14 || operation == tcp_server_op_ESTABLISHED_1_S_15 || operation == tcp_server_op_ESTABLISHED_S_6 || operation == tcp_server_op_ESTABLISHED_S_7 || operation == tcp_server_op_ESTABLISHED_S_8 || operation == tcp_server_op_ESTABLISHED_S_10 || operation == tcp_server_op_ESTABLISHED_S_11 || operation == tcp_server_op_ESTABLISHED_S_12 || operation == tcp_server_op_ESTABLISHED_S_9 || operation == tcp_server_op_ESTABLISHED_S_13)
        local_seq <= tx_ctl_loc_seq_in;
      else if (operation == tcp_server_op_LISTEN_S_3)
        local_seq <= 'h7D0;
      else if (operation == tcp_server_op_SYN_RCVD_1_S_5)
        local_seq <= (1 + local_seq);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      remote_port <= 16'd0;
    else begin
      if (operation == tcp_server_op_LISTEN_S_3)
        remote_port <= src_port_in;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      ACK_out <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18 || operation == tcp_server_op_ABSTRACT_S_19 || operation == tcp_server_op_ABSTRACT_S_21 || operation == tcp_server_op_ABSTRACT_S_20 || operation == tcp_server_op_RST_RCVD_S_22 || operation == tcp_server_op_SYN_RCVD_S_4)
        ACK_out <= 1;
      else if (operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1)
        ACK_out <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      FIN_out <= 0;
  end

  always_ff @(posedge clk) begin
    if (rst)
      RST_out <= 0;
    else begin
      if (operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1 || operation == tcp_server_op_SYN_RCVD_S_4)
        RST_out <= 0;
      else if (operation == tcp_server_op_RST_RCVD_S_22)
        RST_out <= 1;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      SYN_out <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18 || operation == tcp_server_op_ABSTRACT_S_19 || operation == tcp_server_op_ABSTRACT_S_21 || operation == tcp_server_op_ABSTRACT_S_20 || operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1 || operation == tcp_server_op_RST_RCVD_S_22)
        SYN_out <= 0;
      else if (operation == tcp_server_op_SYN_RCVD_S_4)
        SYN_out <= 1;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      ack_number_out <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18 || operation == tcp_server_op_ABSTRACT_S_19)
        ack_number_out <= 32'((64'd1 + ({ 'h0, local_ack})));
      else if (operation == tcp_server_op_ABSTRACT_S_21 || operation == tcp_server_op_ABSTRACT_S_20 || operation == tcp_server_op_RST_RCVD_S_22 || operation == tcp_server_op_SYN_RCVD_S_4)
        ack_number_out <= local_ack;
      else if (operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1)
        ack_number_out <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      dst_port_out <= 16'd0;
    else begin
      if (operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1)
        dst_port_out <= 16'd0;
      else if (operation == tcp_server_op_SYN_RCVD_S_4)
        dst_port_out <= remote_port;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      seq_number_out <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18 || operation == tcp_server_op_ABSTRACT_S_19 || operation == tcp_server_op_ABSTRACT_S_21 || operation == tcp_server_op_ABSTRACT_S_20 || operation == tcp_server_op_RST_RCVD_S_22 || operation == tcp_server_op_SYN_RCVD_S_4)
        seq_number_out <= local_seq;
      else if (operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1)
        seq_number_out <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      src_port_out <= 16'd0;
    else begin
      if (operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1)
        src_port_out <= 16'd0;
      else if (operation == tcp_server_op_SYN_RCVD_S_4)
        src_port_out <= local_port;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      ACK_port_2_rdy <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18 || operation == tcp_server_op_ABSTRACT_S_19 || operation == tcp_server_op_ABSTRACT_S_21 || operation == tcp_server_op_ABSTRACT_S_20 || operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1 || operation == tcp_server_op_ESTABLISHED_1_S_14 || operation == tcp_server_op_ESTABLISHED_1_S_15 || operation == tcp_server_op_ESTABLISHED_S_6 || operation == tcp_server_op_ESTABLISHED_S_7 || operation == tcp_server_op_ESTABLISHED_S_8 || operation == tcp_server_op_ESTABLISHED_S_10 || operation == tcp_server_op_ESTABLISHED_S_11 || operation == tcp_server_op_ESTABLISHED_S_12 || operation == tcp_server_op_ESTABLISHED_S_9 || operation == tcp_server_op_ESTABLISHED_S_13 || operation == tcp_server_op_FLUSH_S_17 || operation == tcp_server_op_FLUSH_S_16 || operation == tcp_server_op_wait_FLUSH_S || operation == tcp_server_op_LISTEN_S_3 || operation == tcp_server_op_wait_LISTEN_S || operation == tcp_server_op_RST_RCVD_S_22 || operation == tcp_server_op_SYN_RCVD_1_S_5)
        ACK_port_2_rdy <= 0;
      else if (operation == tcp_server_op_wait_SYN_RCVD_1_S || operation == tcp_server_op_SYN_RCVD_S_4)
        ACK_port_2_rdy <= 1;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      ACK_port_3_rdy <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18 || operation == tcp_server_op_ABSTRACT_S_19 || operation == tcp_server_op_ABSTRACT_S_21 || operation == tcp_server_op_ABSTRACT_S_20 || operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1 || operation == tcp_server_op_ESTABLISHED_S_6 || operation == tcp_server_op_ESTABLISHED_S_7 || operation == tcp_server_op_ESTABLISHED_S_8 || operation == tcp_server_op_ESTABLISHED_S_10 || operation == tcp_server_op_ESTABLISHED_S_11 || operation == tcp_server_op_ESTABLISHED_S_12 || operation == tcp_server_op_ESTABLISHED_S_9 || operation == tcp_server_op_ESTABLISHED_S_13 || operation == tcp_server_op_FLUSH_S_17 || operation == tcp_server_op_FLUSH_S_16 || operation == tcp_server_op_LISTEN_S_3 || operation == tcp_server_op_wait_LISTEN_S || operation == tcp_server_op_RST_RCVD_S_22 || operation == tcp_server_op_SYN_RCVD_1_S_5 || operation == tcp_server_op_wait_SYN_RCVD_1_S || operation == tcp_server_op_SYN_RCVD_S_4)
        ACK_port_3_rdy <= 0;
      else if (operation == tcp_server_op_ESTABLISHED_1_S_14 || operation == tcp_server_op_ESTABLISHED_1_S_15 || operation == tcp_server_op_wait_FLUSH_S)
        ACK_port_3_rdy <= 1;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      ACK_port_rdy <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18 || operation == tcp_server_op_ABSTRACT_S_19 || operation == tcp_server_op_ABSTRACT_S_21 || operation == tcp_server_op_ABSTRACT_S_20 || operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1 || operation == tcp_server_op_ESTABLISHED_1_S_14 || operation == tcp_server_op_ESTABLISHED_1_S_15 || operation == tcp_server_op_ESTABLISHED_S_6 || operation == tcp_server_op_ESTABLISHED_S_7 || operation == tcp_server_op_ESTABLISHED_S_8 || operation == tcp_server_op_ESTABLISHED_S_10 || operation == tcp_server_op_ESTABLISHED_S_11 || operation == tcp_server_op_ESTABLISHED_S_12 || operation == tcp_server_op_ESTABLISHED_S_9 || operation == tcp_server_op_ESTABLISHED_S_13 || operation == tcp_server_op_FLUSH_S_17 || operation == tcp_server_op_FLUSH_S_16 || operation == tcp_server_op_wait_FLUSH_S || operation == tcp_server_op_LISTEN_S_3 || operation == tcp_server_op_wait_LISTEN_S || operation == tcp_server_op_RST_RCVD_S_22 || operation == tcp_server_op_SYN_RCVD_1_S_5 || operation == tcp_server_op_wait_SYN_RCVD_1_S || operation == tcp_server_op_SYN_RCVD_S_4)
        ACK_port_rdy <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      SYN_port_2_rdy <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18 || operation == tcp_server_op_ABSTRACT_S_19 || operation == tcp_server_op_ABSTRACT_S_21 || operation == tcp_server_op_ABSTRACT_S_20 || operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_CLOSED_S_1 || operation == tcp_server_op_ESTABLISHED_1_S_14 || operation == tcp_server_op_ESTABLISHED_1_S_15 || operation == tcp_server_op_ESTABLISHED_S_6 || operation == tcp_server_op_ESTABLISHED_S_7 || operation == tcp_server_op_ESTABLISHED_S_8 || operation == tcp_server_op_ESTABLISHED_S_10 || operation == tcp_server_op_ESTABLISHED_S_11 || operation == tcp_server_op_ESTABLISHED_S_12 || operation == tcp_server_op_ESTABLISHED_S_9 || operation == tcp_server_op_ESTABLISHED_S_13 || operation == tcp_server_op_FLUSH_S_17 || operation == tcp_server_op_FLUSH_S_16 || operation == tcp_server_op_wait_FLUSH_S || operation == tcp_server_op_LISTEN_S_3 || operation == tcp_server_op_wait_LISTEN_S || operation == tcp_server_op_RST_RCVD_S_22 || operation == tcp_server_op_SYN_RCVD_1_S_5 || operation == tcp_server_op_wait_SYN_RCVD_1_S || operation == tcp_server_op_SYN_RCVD_S_4)
        SYN_port_2_rdy <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      SYN_port_rdy <= 0;
    else begin
      if (operation == tcp_server_op_ABSTRACT_S_18 || operation == tcp_server_op_ABSTRACT_S_19 || operation == tcp_server_op_ABSTRACT_S_21 || operation == tcp_server_op_ABSTRACT_S_20 || operation == tcp_server_op_CLOSED_S_2 || operation == tcp_server_op_ESTABLISHED_1_S_14 || operation == tcp_server_op_ESTABLISHED_1_S_15 || operation == tcp_server_op_ESTABLISHED_S_6 || operation == tcp_server_op_ESTABLISHED_S_7 || operation == tcp_server_op_ESTABLISHED_S_8 || operation == tcp_server_op_ESTABLISHED_S_10 || operation == tcp_server_op_ESTABLISHED_S_11 || operation == tcp_server_op_ESTABLISHED_S_12 || operation == tcp_server_op_ESTABLISHED_S_9 || operation == tcp_server_op_ESTABLISHED_S_13 || operation == tcp_server_op_FLUSH_S_17 || operation == tcp_server_op_FLUSH_S_16 || operation == tcp_server_op_wait_FLUSH_S || operation == tcp_server_op_LISTEN_S_3 || operation == tcp_server_op_RST_RCVD_S_22 || operation == tcp_server_op_SYN_RCVD_1_S_5 || operation == tcp_server_op_wait_SYN_RCVD_1_S || operation == tcp_server_op_SYN_RCVD_S_4)
        SYN_port_rdy <= 0;
      else if (operation == tcp_server_op_CLOSED_S_1 || operation == tcp_server_op_wait_LISTEN_S)
        SYN_port_rdy <= 1;
    end
  end

  assign abstract_port_vld_out = abstract_port_vld;
  assign close_reset_out       = close_reset;
  assign dcn_send_ack_out      = dcn_send_ack;
  assign local_port_out        = local_port;
  assign remote_port_out       = remote_port;

endmodule
