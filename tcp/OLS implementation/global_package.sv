// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.04.2025 at 16:09                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package global_package;

  typedef enum logic unsigned [0:0] { ACTIVE_OPEN } e_events;

  typedef enum logic unsigned [3:0] { CLOSED, LISTEN, RST_RCVD, FLUSH, SYN_RCVD, SYN_RCVD_1, ESTABLISHED, ESTABLISHED_1, ABSTRACTED_STATE } e_states;

endpackage
