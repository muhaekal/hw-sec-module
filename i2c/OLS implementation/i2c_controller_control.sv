// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 21.03.2025 at 11:38                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import global_package::*;
import i2c_controller_operations::*;


module i2c_controller_control #(
    parameter THD_STA=4, parameter TLOW=5, parameter THIGH=4, parameter TSU_DAT=2, parameter TSU_STO=4, parameter THIGH_SAMPLE=1
)(
  input  logic                       rst,
  input  logic                       clk,
  input  logic unsigned [0:0]        start,
  input  logic unsigned [0:0]        ack,
  input  logic unsigned [3:0]        bit_count_addr,
  input  logic unsigned [3:0]        bit_count_data,
  input  logic unsigned [9:0]        count_thd,
  input  logic unsigned [9:0]        count_thigh,
  input  logic unsigned [9:0]        count_tlow,
  input  logic unsigned [1:0]        rcvd_byte,
  input  logic unsigned [0:0]        rw,
  input  logic unsigned [1:0]        sent_byte,
  output i2c_controller_operations_t operation
);

  typedef enum { i2c_controller_IDLE_S, i2c_controller_START_S, i2c_controller_LOW_CLK_ADDR_S, i2c_controller_HIGH_CLK_ADDR_S, i2c_controller_LOW_ADDR_ACK_S, i2c_controller_HIGH_ADDR_ACK_S, i2c_controller_LOW_CLK_DATA_S, i2c_controller_HIGH_CLK_DATA_S, i2c_controller_LOW_DATA_ACK_S, i2c_controller_HIGH_DATA_ACK_S, i2c_controller_LOW_STOP_S, i2c_controller_HIGH_STOP_S } i2c_controller_states_t;

  i2c_controller_states_t current_state;
  i2c_controller_states_t next_state;

  always @(current_state, start, ack, bit_count_addr, bit_count_data, count_thd, count_thigh, count_tlow, rcvd_byte, rw, sent_byte)
  begin
    case (current_state)
      i2c_controller_IDLE_S:
        begin
          if ((start != 1'd0)) begin
            operation <= i2c_controller_op_IDLE_S_1;
            next_state <= i2c_controller_START_S;
          end else if ((start == 1'd0)) begin
            operation <= i2c_controller_op_IDLE_S_2;
            next_state <= i2c_controller_IDLE_S;
          end
        end
      i2c_controller_START_S:
        begin
          if ((({ 54'h0, count_thd}) < THD_STA)) begin
            operation <= i2c_controller_op_START_S_3;
            next_state <= i2c_controller_START_S;
          end else if ((({ 54'h0, count_thd}) >= THD_STA)) begin
            operation <= i2c_controller_op_START_S_4;
            next_state <= i2c_controller_LOW_CLK_ADDR_S;
          end
        end
      i2c_controller_LOW_CLK_ADDR_S:
        begin
          if (1 && (count_tlow == (TLOW-TSU_DAT))) begin
            operation <= i2c_controller_op_LOW_CLK_ADDR_S_5;
            next_state <= i2c_controller_LOW_CLK_ADDR_S;
          end else if ((({ 54'h0, count_tlow}) < TLOW) && (count_tlow != (TLOW-TSU_DAT))) begin
            operation <= i2c_controller_op_LOW_CLK_ADDR_S_6;
            next_state <= i2c_controller_LOW_CLK_ADDR_S;
          end else if ((({ 54'h0, count_tlow}) >= TLOW)) begin
            operation <= i2c_controller_op_LOW_CLK_ADDR_S_7;
            next_state <= i2c_controller_HIGH_CLK_ADDR_S;
          end
        end
      i2c_controller_HIGH_CLK_ADDR_S:
        begin
          if ((({ 54'h0, count_thigh}) < THIGH)) begin
            operation <= i2c_controller_op_HIGH_CLK_ADDR_S_8;
            next_state <= i2c_controller_HIGH_CLK_ADDR_S;
          end else if ((({ 54'h0, count_thigh}) >= THIGH) && (({ 60'h0, bit_count_addr}) < 64'd8)) begin
            operation <= i2c_controller_op_HIGH_CLK_ADDR_S_9;
            next_state <= i2c_controller_LOW_CLK_ADDR_S;
          end else if ((({ 54'h0, count_thigh}) >= THIGH) && (({ 60'h0, bit_count_addr}) >= 64'd8)) begin
            operation <= i2c_controller_op_HIGH_CLK_ADDR_S_10;
            next_state <= i2c_controller_LOW_ADDR_ACK_S;
          end
        end
      i2c_controller_LOW_ADDR_ACK_S:
        begin
          if ((({ 54'h0, count_tlow}) < TLOW)) begin
            operation <= i2c_controller_op_LOW_ADDR_ACK_S_11;
            next_state <= i2c_controller_LOW_ADDR_ACK_S;
          end else if ((({ 54'h0, count_tlow}) >= TLOW)) begin
            operation <= i2c_controller_op_LOW_ADDR_ACK_S_12;
            next_state <= i2c_controller_HIGH_ADDR_ACK_S;
          end
        end
      i2c_controller_HIGH_ADDR_ACK_S:
        begin
          if (1 && (count_thigh == THIGH_SAMPLE)) begin
            operation <= i2c_controller_op_HIGH_ADDR_ACK_S_13;
            next_state <= i2c_controller_HIGH_ADDR_ACK_S;
          end else if ((({ 54'h0, count_thigh}) < THIGH) && (count_thigh != THIGH_SAMPLE)) begin
            operation <= i2c_controller_op_HIGH_ADDR_ACK_S_14;
            next_state <= i2c_controller_HIGH_ADDR_ACK_S;
          end else if ((({ 54'h0, count_thigh}) >= THIGH)) begin
            operation <= i2c_controller_op_HIGH_ADDR_ACK_S_15;
            next_state <= i2c_controller_LOW_CLK_DATA_S;
          end
        end
      i2c_controller_LOW_CLK_DATA_S:
        begin
          if ((ack != 1'd0)) begin
            operation <= i2c_controller_op_LOW_CLK_DATA_S_16;
            next_state <= i2c_controller_LOW_STOP_S;
          end else if ((ack == 1'd0) && 1 && (count_tlow == (TLOW-TSU_DAT)) && (rw == 1'd0)) begin
            operation <= i2c_controller_op_LOW_CLK_DATA_S_17;
            next_state <= i2c_controller_LOW_CLK_DATA_S;
          end else if ((ack == 1'd0) && (({ 54'd0, count_tlow}) < TLOW) && (rw == 1'd1)) begin
            operation <= i2c_controller_op_LOW_CLK_DATA_S_18;
            next_state <= i2c_controller_LOW_CLK_DATA_S;
          end else if ((ack == 1'd0) && (({ 54'd0, count_tlow}) < TLOW) && (count_tlow != (TLOW-TSU_DAT)) && (rw != 1'd1)) begin
            operation <= i2c_controller_op_LOW_CLK_DATA_S_19;
            next_state <= i2c_controller_LOW_CLK_DATA_S;
          end else if ((ack == 1'd0) && (({ 54'd0, count_tlow}) >= TLOW)) begin
            operation <= i2c_controller_op_LOW_CLK_DATA_S_20;
            next_state <= i2c_controller_HIGH_CLK_DATA_S;
          end
        end
      i2c_controller_HIGH_CLK_DATA_S:
        begin
          if (1 && (count_thigh == THIGH_SAMPLE) && (rw != 1'd0)) begin
            operation <= i2c_controller_op_HIGH_CLK_DATA_S_21;
            next_state <= i2c_controller_HIGH_CLK_DATA_S;
          end else if ((({ 54'd0, count_thigh}) < THIGH) && !(((count_thigh == THIGH_SAMPLE) && (rw != 1'd0)))) begin
            operation <= i2c_controller_op_HIGH_CLK_DATA_S_22;
            next_state <= i2c_controller_HIGH_CLK_DATA_S;
          end else if ((({ 54'h0, count_thigh}) >= THIGH) && (({ 60'h0, bit_count_data}) < 64'd8)) begin
            operation <= i2c_controller_op_HIGH_CLK_DATA_S_23;
            next_state <= i2c_controller_LOW_CLK_DATA_S;
          end else if ((({ 54'h0, count_thigh}) >= THIGH) && (({ 60'h0, bit_count_data}) >= 64'd8)) begin
            operation <= i2c_controller_op_HIGH_CLK_DATA_S_24;
            next_state <= i2c_controller_LOW_DATA_ACK_S;
          end
        end
      i2c_controller_LOW_DATA_ACK_S:
        begin
          if (1 && (count_tlow == (TLOW-TSU_DAT)) && (rw == 1'd1) && (rcvd_byte != 2'h2)) begin
            operation <= i2c_controller_op_LOW_DATA_ACK_S_25;
            next_state <= i2c_controller_LOW_DATA_ACK_S;
          end else if (1 && (count_tlow == (TLOW-TSU_DAT)) && (rw == 1'd1) && (rcvd_byte == 2'h2)) begin
            operation <= i2c_controller_op_LOW_DATA_ACK_S_26;
            next_state <= i2c_controller_LOW_DATA_ACK_S;
          end else if ((({ 54'd0, count_tlow}) < TLOW) && (rw == 1'd0)) begin
            operation <= i2c_controller_op_LOW_DATA_ACK_S_27;
            next_state <= i2c_controller_LOW_DATA_ACK_S;
          end else if ((({ 54'd0, count_tlow}) < TLOW) && (count_tlow != (TLOW-TSU_DAT)) && (rw != 1'd0)) begin
            operation <= i2c_controller_op_LOW_DATA_ACK_S_28;
            next_state <= i2c_controller_LOW_DATA_ACK_S;
          end else if ((({ 54'h0, count_tlow}) >= TLOW)) begin
            operation <= i2c_controller_op_LOW_DATA_ACK_S_29;
            next_state <= i2c_controller_HIGH_DATA_ACK_S;
          end
        end
      i2c_controller_HIGH_DATA_ACK_S:
        begin
          if (1 && (count_thigh == THIGH_SAMPLE) && (rw == 1'd0)) begin
            operation <= i2c_controller_op_HIGH_DATA_ACK_S_30;
            next_state <= i2c_controller_HIGH_DATA_ACK_S;
          end else if ((({ 54'd0, count_thigh}) < THIGH) && !(((count_thigh == THIGH_SAMPLE) && (rw == 1'd0)))) begin
            operation <= i2c_controller_op_HIGH_DATA_ACK_S_31;
            next_state <= i2c_controller_HIGH_DATA_ACK_S;
          end else if ((({ 54'd0, count_thigh}) >= THIGH) && (((rw == 1'd1) && (rcvd_byte == 2'd3)) || ((rw == 1'd0) && (sent_byte == 2'd3)))) begin
            operation <= i2c_controller_op_HIGH_DATA_ACK_S_32;
            next_state <= i2c_controller_LOW_STOP_S;
          end else if ((({ 54'd0, count_thigh}) >= THIGH) && !(((rw == 1'd1) && (rcvd_byte == 2'd3))) && !(((rw == 1'd0) && (sent_byte == 2'd3)))) begin
            operation <= i2c_controller_op_HIGH_DATA_ACK_S_33;
            next_state <= i2c_controller_LOW_CLK_DATA_S;
          end
        end
      i2c_controller_LOW_STOP_S:
        begin
          if (1 && (count_tlow == (TLOW-TSU_DAT))) begin
            operation <= i2c_controller_op_LOW_STOP_S_34;
            next_state <= i2c_controller_LOW_STOP_S;
          end else if ((({ 54'h0, count_tlow}) < TLOW) && (count_tlow != (TLOW-TSU_DAT))) begin
            operation <= i2c_controller_op_LOW_STOP_S_35;
            next_state <= i2c_controller_LOW_STOP_S;
          end else if ((({ 54'h0, count_tlow}) >= TLOW)) begin
            operation <= i2c_controller_op_LOW_STOP_S_36;
            next_state <= i2c_controller_HIGH_STOP_S;
          end
        end
      i2c_controller_HIGH_STOP_S:
        begin
          if ((({ 54'h0, count_thigh}) < THIGH) && (count_thigh != TSU_STO)) begin
            operation <= i2c_controller_op_HIGH_STOP_S_37;
            next_state <= i2c_controller_HIGH_STOP_S;
          end else if ((({ 54'h0, count_thigh}) >= THIGH)) begin
            operation <= i2c_controller_op_HIGH_STOP_S_38;
            next_state <= i2c_controller_IDLE_S;
          end
        end
    endcase
  end

  always_ff @(posedge clk)
  begin
    if (rst == 1) begin
      current_state <= i2c_controller_IDLE_S;
    end else begin
      current_state <= next_state;
    end
  end

endmodule
