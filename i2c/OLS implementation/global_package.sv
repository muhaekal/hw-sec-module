// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.03.2025 at 11:38                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package global_package;

  typedef enum logic unsigned [3:0] { IDLE, START, LOW_CLK_ADDR, HIGH_CLK_ADDR, LOW_ADDR_ACK, HIGH_ADDR_ACK, LOW_CLK_DATA, HIGH_CLK_DATA, LOW_DATA_ACK, HIGH_DATA_ACK, LOW_STOP, HIGH_STOP } e_states;

endpackage
