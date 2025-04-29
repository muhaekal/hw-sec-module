// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.04.2025 at 11:36                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package tcp_server_operations;

  typedef enum logic unsigned [4:0] { tcp_server_op_ABSTRACT_S_19, tcp_server_op_ABSTRACT_S_18, tcp_server_op_CLOSED_S_2, tcp_server_op_CLOSED_S_1, tcp_server_op_ESTABLISHED_1_S_14, tcp_server_op_ESTABLISHED_1_S_15, tcp_server_op_ESTABLISHED_S_6, tcp_server_op_ESTABLISHED_S_7, tcp_server_op_ESTABLISHED_S_8, tcp_server_op_ESTABLISHED_S_10, tcp_server_op_ESTABLISHED_S_11, tcp_server_op_ESTABLISHED_S_12, tcp_server_op_ESTABLISHED_S_9, tcp_server_op_ESTABLISHED_S_13, tcp_server_op_FLUSH_S_17, tcp_server_op_FLUSH_S_16, tcp_server_op_wait_FLUSH_S, tcp_server_op_LISTEN_S_3, tcp_server_op_wait_LISTEN_S, tcp_server_op_RST_RCVD_S_20, tcp_server_op_SYN_RCVD_1_S_5, tcp_server_op_wait_SYN_RCVD_1_S, tcp_server_op_SYN_RCVD_S_4 } tcp_server_operations_t;

endpackage
