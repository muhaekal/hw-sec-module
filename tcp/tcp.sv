module tcp_server (
    input  logic        clk,         // Clock
    input  logic        rst_n,       // Active-low reset
    input  logic [31:0] rx_data,     // Incoming TCP segment
    input  logic        rx_valid,    // Valid signal for incoming data
    output logic [31:0] tx_data,     // Outgoing TCP segment
    output logic        tx_valid     // Valid signal for outgoing data
);

    // TCP States as per RFC 9293
    typedef enum logic [2:0] {
        CLOSED, LISTEN, SYN_RECEIVED, ESTABLISHED, FIN_WAIT_1, FIN_WAIT_2,
        CLOSE_WAIT, LAST_ACK, TIME_WAIT
    } tcp_state_t;

    tcp_state_t state;
    logic [31:0] seq_num, ack_num;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state    <= CLOSED;
            seq_num  <= 0;
            ack_num  <= 0;
            tx_valid <= 0;
        end else begin
            case (state)
                CLOSED: begin
                    state <= LISTEN;
                end

                LISTEN: begin
                    if (rx_valid && (rx_data[31:24] == 8'h02)) begin // SYN Received
                        seq_num  <= rx_data[23:0] + 1;
                        tx_data  <= {8'h12, seq_num}; // SYN-ACK
                        tx_valid <= 1;
                        state    <= SYN_RECEIVED;
                    end
                end

                SYN_RECEIVED: begin
                    if (rx_valid && (rx_data[31:24] == 8'h10)) begin // ACK Received
                        tx_valid <= 0;
                        state    <= ESTABLISHED;
                    end
                end

                ESTABLISHED: begin
                    if (rx_valid) begin
                        if (rx_data[31:24] == 8'h01) begin // FIN Received
                            tx_data  <= {8'h10, rx_data[23:0] + 1}; // ACK
                            tx_valid <= 1;
                            state    <= CLOSE_WAIT;
                        end else begin
                            seq_num  <= rx_data[23:0] + 1;
                            tx_data  <= {8'h10, seq_num}; // ACK Data
                            tx_valid <= 1;
                        end
                    end
                end

                CLOSE_WAIT: begin
                    tx_data  <= {8'h01, seq_num}; // Send FIN
                    tx_valid <= 1;
                    state    <= LAST_ACK;
                end

                LAST_ACK: begin
                    if (rx_valid && (rx_data[31:24] == 8'h10)) begin // ACK Received
                        state    <= CLOSED;
                        tx_valid <= 0;
                    end
                end

                default: state <= CLOSED;
            endcase
        end
    end
endmodule
