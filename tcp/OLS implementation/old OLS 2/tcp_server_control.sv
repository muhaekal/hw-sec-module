// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.04.2025 at 11:36                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import global_package::*;
import tcp_server_operations::*;


module tcp_server_control (
  input  logic                   rst,
  input  logic                   clk,
  input  logic                   FIN_in,
  input  logic                   RST_in,
  input  logic unsigned [15:0]   dst_port_in,
  input  logic                   force_dcn_in,
  input  logic                   listen_in,
  input  logic unsigned [15:0]   src_port_in,
  input  logic                   tx_done_in,
  input  logic                   ACK_port_2_vld,
  input  logic                   ACK_port_3_vld,
  input  logic                   SYN_port_vld,
  input  logic                   abstract_port_vld,
  input  logic                   close_reset,
  input  logic unsigned [15:0]   local_port,
  input  logic unsigned [15:0]   remote_port,
  output tcp_server_operations_t operation
);

  typedef enum { tcp_server_CLOSED_S, tcp_server_LISTEN_S, tcp_server_SYN_RCVD_S, tcp_server_SYN_RCVD_1_S, tcp_server_ESTABLISHED_S, tcp_server_ESTABLISHED_1_S, tcp_server_FLUSH_S, tcp_server_ABSTRACT_S, tcp_server_RST_RCVD_S } tcp_server_states_t;

  tcp_server_states_t current_state;
  tcp_server_states_t next_state;

  always @(current_state, FIN_in, RST_in, dst_port_in, force_dcn_in, listen_in, src_port_in, tx_done_in, ACK_port_2_vld, ACK_port_3_vld, SYN_port_vld, abstract_port_vld, close_reset, local_port, remote_port)
  begin
    case (current_state)
      tcp_server_CLOSED_S:
        begin
          if (listen_in) begin
            operation <= tcp_server_op_CLOSED_S_1;
            next_state <= tcp_server_LISTEN_S;
          end else if (!(listen_in)) begin
            operation <= tcp_server_op_CLOSED_S_2;
            next_state <= tcp_server_CLOSED_S;
          end
        end
      tcp_server_LISTEN_S:
        begin
          if (SYN_port_vld) begin
            operation <= tcp_server_op_LISTEN_S_3;
            next_state <= tcp_server_SYN_RCVD_S;
          end else if (!(SYN_port_vld)) begin
            operation <= tcp_server_op_wait_LISTEN_S;
            next_state <= tcp_server_LISTEN_S;
          end
        end
      tcp_server_SYN_RCVD_S:
        begin
          if (1) begin
            operation <= tcp_server_op_SYN_RCVD_S_4;
            next_state <= tcp_server_SYN_RCVD_1_S;
          end
        end
      tcp_server_SYN_RCVD_1_S:
        begin
          if (ACK_port_2_vld) begin
            operation <= tcp_server_op_SYN_RCVD_1_S_5;
            next_state <= tcp_server_ESTABLISHED_S;
          end else if (!(ACK_port_2_vld)) begin
            operation <= tcp_server_op_wait_SYN_RCVD_1_S;
            next_state <= tcp_server_SYN_RCVD_1_S;
          end
        end
      tcp_server_ESTABLISHED_S:
        begin
          if (tx_done_in && (!(listen_in) || force_dcn_in)) begin
            operation <= tcp_server_op_ESTABLISHED_S_6;
            next_state <= tcp_server_ESTABLISHED_1_S;
          end else if (tx_done_in && listen_in && !(force_dcn_in) && FIN_in && (src_port_in == remote_port) && (dst_port_in == local_port)) begin
            operation <= tcp_server_op_ESTABLISHED_S_7;
            next_state <= tcp_server_ESTABLISHED_1_S;
          end else if (tx_done_in && listen_in && !(force_dcn_in) && !(((FIN_in && (src_port_in == remote_port)) && (dst_port_in == local_port))) && RST_in && (src_port_in == remote_port) && (dst_port_in == local_port)) begin
            operation <= tcp_server_op_ESTABLISHED_S_8;
            next_state <= tcp_server_ESTABLISHED_1_S;
          end else if (tx_done_in && listen_in && !(force_dcn_in) && !(((FIN_in && (src_port_in == remote_port)) && (dst_port_in == local_port))) && !(((RST_in && (src_port_in == remote_port)) && (dst_port_in == local_port)))) begin
            operation <= tcp_server_op_ESTABLISHED_S_9;
            next_state <= tcp_server_ESTABLISHED_S;
          end else if (!(tx_done_in) && (!(listen_in) || force_dcn_in)) begin
            operation <= tcp_server_op_ESTABLISHED_S_10;
            next_state <= tcp_server_ESTABLISHED_1_S;
          end else if (!(tx_done_in) && listen_in && !(force_dcn_in) && FIN_in && (src_port_in == remote_port) && (dst_port_in == local_port)) begin
            operation <= tcp_server_op_ESTABLISHED_S_11;
            next_state <= tcp_server_ESTABLISHED_1_S;
          end else if (!(tx_done_in) && listen_in && !(force_dcn_in) && !(((FIN_in && (src_port_in == remote_port)) && (dst_port_in == local_port))) && RST_in && (src_port_in == remote_port) && (dst_port_in == local_port)) begin
            operation <= tcp_server_op_ESTABLISHED_S_12;
            next_state <= tcp_server_ESTABLISHED_1_S;
          end else if (!(tx_done_in) && listen_in && !(force_dcn_in) && !(((FIN_in && (src_port_in == remote_port)) && (dst_port_in == local_port))) && !(((RST_in && (src_port_in == remote_port)) && (dst_port_in == local_port)))) begin
            operation <= tcp_server_op_ESTABLISHED_S_13;
            next_state <= tcp_server_ESTABLISHED_S;
          end
        end
      tcp_server_ESTABLISHED_1_S:
        begin
          if (tx_done_in) begin
            operation <= tcp_server_op_ESTABLISHED_1_S_14;
            next_state <= tcp_server_FLUSH_S;
          end else if (!(tx_done_in)) begin
            operation <= tcp_server_op_ESTABLISHED_1_S_15;
            next_state <= tcp_server_FLUSH_S;
          end
        end
      tcp_server_FLUSH_S:
        begin
          if (ACK_port_3_vld && close_reset) begin
            operation <= tcp_server_op_FLUSH_S_16;
            next_state <= tcp_server_RST_RCVD_S;
          end else if (ACK_port_3_vld && !(close_reset)) begin
            operation <= tcp_server_op_FLUSH_S_17;
            next_state <= tcp_server_ABSTRACT_S;
          end else if (!(ACK_port_3_vld)) begin
            operation <= tcp_server_op_wait_FLUSH_S;
            next_state <= tcp_server_FLUSH_S;
          end
        end
      tcp_server_ABSTRACT_S:
        begin
          if (abstract_port_vld) begin
            operation <= tcp_server_op_ABSTRACT_S_18;
            next_state <= tcp_server_CLOSED_S;
          end else if (!(abstract_port_vld)) begin
            operation <= tcp_server_op_ABSTRACT_S_19;
            next_state <= tcp_server_ABSTRACT_S;
          end
        end
      tcp_server_RST_RCVD_S:
        begin
          if (1) begin
            operation <= tcp_server_op_RST_RCVD_S_20;
            next_state <= tcp_server_CLOSED_S;
          end
        end
    endcase
  end

  always_ff @(posedge clk)
  begin
    if (rst == 1) begin
      current_state <= tcp_server_CLOSED_S;
    end else begin
      current_state <= next_state;
    end
  end

endmodule
