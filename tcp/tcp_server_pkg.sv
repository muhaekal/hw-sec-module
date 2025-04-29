// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 29.04.2025 at 10:34                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package tcp_server_pkg;


typedef enum logic unsigned [0:0] { ACTIVE_OPEN } e_events;

typedef enum logic unsigned [3:0] { CLOSED = 0, LISTEN = 2, RST_RCVD = 3, FLUSH = 4, SYN_RCVD = 5, SYN_RCVD_1 = 6, ESTABLISHED = 7, ESTABLISHED_1 = 8, ABSTRACTED_STATE = 9 } e_states;


endpackage
