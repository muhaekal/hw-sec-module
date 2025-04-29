// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 04.02.2025 at 12:06                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package tcp_client_pkg;


typedef enum logic unsigned [3:0] { ACTIVE_OPEN, PASSIVE_OPEN, SEND, RECEIVE_SYN, RECEIVE_RST, RECEIVE_SYN_ACK, RECEIVE_FIN, RECEIVE_FIN_ACK, CLOSE } e_events;

typedef enum logic unsigned [3:0] { CLOSED, SYN_SENT, LISTEN, SYN_RCVD, ESTABLISHED, FIN_WAIT_1, FIN_WAIT_2, CLOSING, CLOSE_WAIT, LAST_ACK, TIME_WAIT } e_states;

typedef struct packed {
  logic unsigned [15:0] source_port;
  logic unsigned [15:0] destination_port;
  logic unsigned [31:0] seq_number;
  logic unsigned [31:0] ack_number;
  logic unsigned [3:0] data_offset;
  logic URG;
  logic ACK;
  logic PSH;
  logic RST;
  logic SYN;
  logic FIN;
  logic unsigned [15:0] checksum;
  logic unsigned [15:0] urgent_pointer;
} st_TCP_Header;


endpackage
