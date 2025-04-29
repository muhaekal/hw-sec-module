// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.03.2025 at 11:38                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import global_package::*;
import i2c_controller_operations::*;


module i2c_controller_computational (
  input  logic                       rst,
  input  logic                       clk,
  input  logic unsigned [7:0]        addr,
  output logic unsigned [23:0]       data_rcv,
  input  logic unsigned [23:0]       data_rcv_in,
  input  logic unsigned [23:0]       data_snt,
  output logic unsigned [0:0]        scl,
  input  logic unsigned [0:0]        sda_in,
  output logic unsigned [0:0]        sda_out,
  input  logic unsigned [0:0]        start,
  output logic unsigned [0:0]        ack_out,
  output logic unsigned [3:0]        bit_count_addr_out,
  output logic unsigned [3:0]        bit_count_data_out,
  output logic unsigned [9:0]        count_thd_out,
  output logic unsigned [9:0]        count_thigh_out,
  output logic unsigned [9:0]        count_tlow_out,
  output logic unsigned [1:0]        rcvd_byte_out,
  output logic unsigned [0:0]        rw_out,
  output logic unsigned [1:0]        sent_byte_out,
  input  i2c_controller_operations_t operation
);

  logic unsigned [0:0]  ack;
  logic unsigned [7:0]  addr_shift_reg;
  logic unsigned [3:0]  bit_count_addr;
  logic unsigned [3:0]  bit_count_data;
  logic unsigned [9:0]  count_thd;
  logic unsigned [9:0]  count_thigh;
  logic unsigned [9:0]  count_tlow;
  logic unsigned [23:0] data_shift_reg;
  logic unsigned [1:0]  rcvd_byte;
  logic unsigned [0:0]  rw;
  logic unsigned [1:0]  sent_byte;

  always_ff @(posedge clk) begin
    if (rst)
      ack <= 1'd0;
    else begin
      if (operation == i2c_controller_op_HIGH_ADDR_ACK_S_13 || operation == i2c_controller_op_HIGH_DATA_ACK_S_30)
        ack <= sda_in;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      addr_shift_reg <= 8'd0;
    else begin
      if (operation == i2c_controller_op_LOW_CLK_ADDR_S_5)
        addr_shift_reg <= ({ addr_shift_reg[6:0], 1'h0});
      else if (operation == i2c_controller_op_START_S_4 || operation == i2c_controller_op_START_S_3)
        addr_shift_reg <= addr;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      bit_count_addr <= 4'd0;
    else begin
      if (operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_IDLE_S_1 || operation == i2c_controller_op_START_S_4)
        bit_count_addr <= 4'd0;
      else if (operation == i2c_controller_op_LOW_CLK_ADDR_S_5)
        bit_count_addr <= (4'd1 + bit_count_addr);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      bit_count_data <= 4'd0;
    else begin
      if (operation == i2c_controller_op_HIGH_ADDR_ACK_S_15 || operation == i2c_controller_op_HIGH_DATA_ACK_S_30 || operation == i2c_controller_op_HIGH_DATA_ACK_S_31 || operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_IDLE_S_1)
        bit_count_data <= 4'd0;
      else if (operation == i2c_controller_op_HIGH_CLK_DATA_S_21 || operation == i2c_controller_op_LOW_CLK_DATA_S_17)
        bit_count_data <= (4'd1 + bit_count_data);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      count_thd <= 10'd0;
    else begin
      if (operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_IDLE_S_1)
        count_thd <= 10'd0;
      else if (operation == i2c_controller_op_START_S_4 || operation == i2c_controller_op_START_S_3)
        count_thd <= (10'd1 + count_thd);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      count_thigh <= 10'd0;
    else begin
      if (operation == i2c_controller_op_HIGH_ADDR_ACK_S_13 || operation == i2c_controller_op_HIGH_ADDR_ACK_S_14 || operation == i2c_controller_op_HIGH_ADDR_ACK_S_15 || operation == i2c_controller_op_HIGH_CLK_ADDR_S_8 || operation == i2c_controller_op_HIGH_CLK_ADDR_S_10 || operation == i2c_controller_op_HIGH_CLK_ADDR_S_9 || operation == i2c_controller_op_HIGH_CLK_DATA_S_21 || operation == i2c_controller_op_HIGH_CLK_DATA_S_22 || operation == i2c_controller_op_HIGH_CLK_DATA_S_23 || operation == i2c_controller_op_HIGH_CLK_DATA_S_24 || operation == i2c_controller_op_HIGH_DATA_ACK_S_30 || operation == i2c_controller_op_HIGH_DATA_ACK_S_31 || operation == i2c_controller_op_HIGH_DATA_ACK_S_33 || operation == i2c_controller_op_HIGH_DATA_ACK_S_32 || operation == i2c_controller_op_HIGH_STOP_S_37 || operation == i2c_controller_op_HIGH_STOP_S_38)
        count_thigh <= (10'd1 + count_thigh);
      else if (operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_IDLE_S_1 || operation == i2c_controller_op_LOW_ADDR_ACK_S_12 || operation == i2c_controller_op_LOW_ADDR_ACK_S_11 || operation == i2c_controller_op_LOW_CLK_ADDR_S_7 || operation == i2c_controller_op_LOW_CLK_ADDR_S_5 || operation == i2c_controller_op_LOW_CLK_ADDR_S_6 || operation == i2c_controller_op_LOW_CLK_DATA_S_20 || operation == i2c_controller_op_LOW_CLK_DATA_S_17 || operation == i2c_controller_op_LOW_CLK_DATA_S_18 || operation == i2c_controller_op_LOW_CLK_DATA_S_19 || operation == i2c_controller_op_LOW_CLK_DATA_S_16 || operation == i2c_controller_op_LOW_DATA_ACK_S_29 || operation == i2c_controller_op_LOW_DATA_ACK_S_25 || operation == i2c_controller_op_LOW_DATA_ACK_S_26 || operation == i2c_controller_op_LOW_DATA_ACK_S_27 || operation == i2c_controller_op_LOW_DATA_ACK_S_28 || operation == i2c_controller_op_LOW_STOP_S_36 || operation == i2c_controller_op_LOW_STOP_S_34 || operation == i2c_controller_op_LOW_STOP_S_35)
        count_thigh <= 10'd0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      count_tlow <= 10'd0;
    else begin
      if (operation == i2c_controller_op_HIGH_ADDR_ACK_S_13 || operation == i2c_controller_op_HIGH_ADDR_ACK_S_14 || operation == i2c_controller_op_HIGH_ADDR_ACK_S_15 || operation == i2c_controller_op_HIGH_CLK_ADDR_S_8 || operation == i2c_controller_op_HIGH_CLK_ADDR_S_10 || operation == i2c_controller_op_HIGH_CLK_ADDR_S_9 || operation == i2c_controller_op_HIGH_CLK_DATA_S_21 || operation == i2c_controller_op_HIGH_CLK_DATA_S_22 || operation == i2c_controller_op_HIGH_CLK_DATA_S_23 || operation == i2c_controller_op_HIGH_CLK_DATA_S_24 || operation == i2c_controller_op_HIGH_DATA_ACK_S_30 || operation == i2c_controller_op_HIGH_DATA_ACK_S_31 || operation == i2c_controller_op_HIGH_DATA_ACK_S_33 || operation == i2c_controller_op_HIGH_DATA_ACK_S_32 || operation == i2c_controller_op_HIGH_STOP_S_37 || operation == i2c_controller_op_HIGH_STOP_S_38 || operation == i2c_controller_op_START_S_4)
        count_tlow <= 10'd0;
      else if (operation == i2c_controller_op_LOW_ADDR_ACK_S_11 || operation == i2c_controller_op_LOW_CLK_ADDR_S_5 || operation == i2c_controller_op_LOW_CLK_ADDR_S_6 || operation == i2c_controller_op_LOW_CLK_DATA_S_17 || operation == i2c_controller_op_LOW_CLK_DATA_S_18 || operation == i2c_controller_op_LOW_CLK_DATA_S_19 || operation == i2c_controller_op_LOW_CLK_DATA_S_16 || operation == i2c_controller_op_LOW_DATA_ACK_S_25 || operation == i2c_controller_op_LOW_DATA_ACK_S_26 || operation == i2c_controller_op_LOW_DATA_ACK_S_27 || operation == i2c_controller_op_LOW_DATA_ACK_S_28 || operation == i2c_controller_op_LOW_STOP_S_34 || operation == i2c_controller_op_LOW_STOP_S_35)
        count_tlow <= (10'd1 + count_tlow);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      data_shift_reg <= 24'd0;
    else begin
      if (operation == i2c_controller_op_LOW_CLK_DATA_S_17)
        data_shift_reg <= ({ data_shift_reg[22:0], 1'h0});
      else if (operation == i2c_controller_op_START_S_4 || operation == i2c_controller_op_START_S_3)
        data_shift_reg <= data_snt;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      rcvd_byte <= 2'd0;
    else begin
      if (operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_IDLE_S_1 || operation == i2c_controller_op_START_S_4 || operation == i2c_controller_op_START_S_3)
        rcvd_byte <= 2'd0;
      else if (operation == i2c_controller_op_LOW_DATA_ACK_S_25 || operation == i2c_controller_op_LOW_DATA_ACK_S_26)
        rcvd_byte <= (2'd1 + rcvd_byte);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      rw <= 1'd0;
    else begin
      if (operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_IDLE_S_1)
        rw <= 1'd0;
      else if (operation == i2c_controller_op_START_S_4 || operation == i2c_controller_op_START_S_3)
        rw <= addr[0];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      sent_byte <= 2'd0;
    else begin
      if (operation == i2c_controller_op_HIGH_DATA_ACK_S_30)
        sent_byte <= (2'd1 + sent_byte);
      else if (operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_IDLE_S_1 || operation == i2c_controller_op_START_S_4 || operation == i2c_controller_op_START_S_3)
        sent_byte <= 2'd0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      data_rcv <= 24'd0;
    else begin
      if (operation == i2c_controller_op_HIGH_CLK_DATA_S_21)
        data_rcv <= (({ data_rcv_in[22:0], 1'h0}) | sda_in);
      else if (operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_IDLE_S_1)
        data_rcv <= 24'd0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      scl <= 1'd1;
    else begin
      if (operation == i2c_controller_op_HIGH_ADDR_ACK_S_13 || operation == i2c_controller_op_HIGH_ADDR_ACK_S_14 || operation == i2c_controller_op_HIGH_ADDR_ACK_S_15 || operation == i2c_controller_op_HIGH_CLK_ADDR_S_8 || operation == i2c_controller_op_HIGH_CLK_ADDR_S_10 || operation == i2c_controller_op_HIGH_CLK_ADDR_S_9 || operation == i2c_controller_op_HIGH_CLK_DATA_S_21 || operation == i2c_controller_op_HIGH_CLK_DATA_S_22 || operation == i2c_controller_op_HIGH_CLK_DATA_S_23 || operation == i2c_controller_op_HIGH_CLK_DATA_S_24 || operation == i2c_controller_op_HIGH_DATA_ACK_S_30 || operation == i2c_controller_op_HIGH_DATA_ACK_S_31 || operation == i2c_controller_op_HIGH_DATA_ACK_S_33 || operation == i2c_controller_op_HIGH_DATA_ACK_S_32 || operation == i2c_controller_op_HIGH_STOP_S_37 || operation == i2c_controller_op_HIGH_STOP_S_38 || operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_LOW_ADDR_ACK_S_12 || operation == i2c_controller_op_LOW_CLK_ADDR_S_7 || operation == i2c_controller_op_LOW_CLK_DATA_S_20 || operation == i2c_controller_op_LOW_DATA_ACK_S_29 || operation == i2c_controller_op_LOW_STOP_S_36 || operation == i2c_controller_op_START_S_4 || operation == i2c_controller_op_START_S_3)
        scl <= 1'd1;
      else if (operation == i2c_controller_op_LOW_ADDR_ACK_S_11 || operation == i2c_controller_op_LOW_CLK_ADDR_S_5 || operation == i2c_controller_op_LOW_CLK_ADDR_S_6 || operation == i2c_controller_op_LOW_CLK_DATA_S_17 || operation == i2c_controller_op_LOW_CLK_DATA_S_18 || operation == i2c_controller_op_LOW_CLK_DATA_S_19 || operation == i2c_controller_op_LOW_CLK_DATA_S_16 || operation == i2c_controller_op_LOW_DATA_ACK_S_25 || operation == i2c_controller_op_LOW_DATA_ACK_S_26 || operation == i2c_controller_op_LOW_DATA_ACK_S_27 || operation == i2c_controller_op_LOW_DATA_ACK_S_28 || operation == i2c_controller_op_LOW_STOP_S_34 || operation == i2c_controller_op_LOW_STOP_S_35)
        scl <= 1'd0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      sda_out <= 1'd1;
    else begin
      if (operation == i2c_controller_op_HIGH_STOP_S_38 || operation == i2c_controller_op_IDLE_S_2 || operation == i2c_controller_op_IDLE_S_1 || operation == i2c_controller_op_LOW_ADDR_ACK_S_12 || operation == i2c_controller_op_LOW_ADDR_ACK_S_11 || operation == i2c_controller_op_LOW_CLK_DATA_S_18 || operation == i2c_controller_op_LOW_DATA_ACK_S_26 || operation == i2c_controller_op_LOW_DATA_ACK_S_27)
        sda_out <= 1'd1;
      else if (operation == i2c_controller_op_LOW_CLK_ADDR_S_5)
        sda_out <= addr_shift_reg[7];
      else if (operation == i2c_controller_op_LOW_CLK_DATA_S_17)
        sda_out <= data_shift_reg[23];
      else if (operation == i2c_controller_op_LOW_DATA_ACK_S_25 || operation == i2c_controller_op_LOW_STOP_S_34 || operation == i2c_controller_op_START_S_4 || operation == i2c_controller_op_START_S_3)
        sda_out <= 1'd0;
    end
  end

  assign ack_out            = ack;
  assign bit_count_addr_out = bit_count_addr;
  assign bit_count_data_out = bit_count_data;
  assign count_thd_out      = count_thd;
  assign count_thigh_out    = count_thigh;
  assign count_tlow_out     = count_tlow;
  assign rcvd_byte_out      = rcvd_byte;
  assign rw_out             = rw;
  assign sent_byte_out      = sent_byte;

endmodule
