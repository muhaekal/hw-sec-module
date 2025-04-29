module tcp_vlg_tx_add 
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter int WAIT_TICKS = 125, // Nagle's algorythm
  parameter int MTU = 1400
)
(
  input  logic       clk,
  input  logic       rst,
  input  tcp_num_t   seq, // current sequence number
  output tcp_pkt_t   pkt,
  output logic       add,
  output logic       pend,
  input  logic       full, // data ram full
  input  logic       flush, // request to flush tcp related RAMs
  input  logic       val, // user inteface (raw TCP stream)
  input  logic [7:0] dat, // user inteface (raw TCP stream)
  input  logic       snd  // user inteface (raw TCP stream)
);

  enum logic [1:0] {idle_s, pend_s} fsm;
  
  logic [31:0] cks;
  logic [7:0]  dat_reg;
  logic add_timeout, add_mtu;
  tcp_num_t seq_reg, start;
  logic [$clog2(WAIT_TICKS+1)-1:0] timeout;
  logic [$clog2(MTU+1)-1:0] ctr; 
  // clear to send flag is set if:
  // 1. tcp is connected
  // 2. packet info RAM isn't full (check msb)
  // 3. transmission data buffer isn't full
  // New data for transmission didn't arrive for WAIT_TICKS
  
  always_comb begin
    add_mtu = (ctr == MTU - 80 - 1); // 60 for tcp header (with options) and another 20 for ipv4. todo: check for correctness
    add_timeout = (timeout == WAIT_TICKS && !val);
    pend = (fsm == pend_s) && (add_timeout || add_mtu || full || snd); // adding packe at next tick
    pkt.length   = ctr; // length equals byte count for current packet
    pkt.cks      = ctr[0] ? cks + {dat_reg, 8'h00} : cks; // this is how payload checksum is calculated
    pkt.exists   = 1; // Every new entry in packet info table is ofc valid
    pkt.tries    = 0; // The packet hasn't been transmittd yet
    pkt.norm_rto = 0;
    pkt.sack_rto = 0;
    pkt.start    = start; // equals expected ack for packet
    pkt.stop     = seq; // equals expected ack for packet
  end
  
  // Packet creation FSM
  always_ff @ (posedge clk) begin
    if (rst) begin
      ctr     <= 0;
      add     <= 0;
      timeout <= 0;
      fsm   <= idle_s;
    end
    else begin
      if (val) dat_reg <= dat;
      case (fsm)
        idle_s : begin
          if (val) begin
            ctr   <= 1;
            fsm <= pend_s;
          end
          seq_reg <= seq; // equals packet's seq
          add     <= 0;
          cks     <= 0;
          timeout <= 0;
        end
        pend_s : begin
         // pend <= 0;
          start <= seq_reg;
          if (val) begin
            ctr <= ctr + 1;
            cks <= (ctr[0]) ? cks + {dat_reg, dat} : cks;
          end
          timeout <= (val) ? 0 : timeout + 1; // reset timeout if new byte arrives (Nagle's algorithm)
          // either of three conditions to add new packet
          if (full || add_timeout || add_mtu || snd) fsm <= idle_s;
        end
        default :;
      endcase
      add <= (pend && !flush); // if flush request received, don't add packet
    end
  end

endmodule : tcp_vlg_tx_add