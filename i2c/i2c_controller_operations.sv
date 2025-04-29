// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.03.2025 at 11:38                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package i2c_controller_operations;

  typedef enum logic unsigned [5:0] { i2c_controller_op_HIGH_ADDR_ACK_S_13, i2c_controller_op_HIGH_ADDR_ACK_S_14, i2c_controller_op_HIGH_ADDR_ACK_S_15, i2c_controller_op_HIGH_CLK_ADDR_S_8, i2c_controller_op_HIGH_CLK_ADDR_S_10, i2c_controller_op_HIGH_CLK_ADDR_S_9, i2c_controller_op_HIGH_CLK_DATA_S_21, i2c_controller_op_HIGH_CLK_DATA_S_22, i2c_controller_op_HIGH_CLK_DATA_S_23, i2c_controller_op_HIGH_CLK_DATA_S_24, i2c_controller_op_HIGH_DATA_ACK_S_30, i2c_controller_op_HIGH_DATA_ACK_S_31, i2c_controller_op_HIGH_DATA_ACK_S_33, i2c_controller_op_HIGH_DATA_ACK_S_32, i2c_controller_op_HIGH_STOP_S_37, i2c_controller_op_HIGH_STOP_S_38, i2c_controller_op_IDLE_S_2, i2c_controller_op_IDLE_S_1, i2c_controller_op_LOW_ADDR_ACK_S_12, i2c_controller_op_LOW_ADDR_ACK_S_11, i2c_controller_op_LOW_CLK_ADDR_S_7, i2c_controller_op_LOW_CLK_ADDR_S_5, i2c_controller_op_LOW_CLK_ADDR_S_6, i2c_controller_op_LOW_CLK_DATA_S_20, i2c_controller_op_LOW_CLK_DATA_S_17, i2c_controller_op_LOW_CLK_DATA_S_18, i2c_controller_op_LOW_CLK_DATA_S_19, i2c_controller_op_LOW_CLK_DATA_S_16, i2c_controller_op_LOW_DATA_ACK_S_29, i2c_controller_op_LOW_DATA_ACK_S_25, i2c_controller_op_LOW_DATA_ACK_S_26, i2c_controller_op_LOW_DATA_ACK_S_27, i2c_controller_op_LOW_DATA_ACK_S_28, i2c_controller_op_LOW_STOP_S_36, i2c_controller_op_LOW_STOP_S_34, i2c_controller_op_LOW_STOP_S_35, i2c_controller_op_START_S_4, i2c_controller_op_START_S_3 } i2c_controller_operations_t;

endpackage
