
#ifndef _UART_TCP_SERVER_
#define _UART_TCP_SERVER_

#include "systemc.h"
#include "/home/muhammad-haekal/.vscode-server/extensions/lubis-eda.lubis-vsc-plugin-1.0.0/DeSCAM/include/interfaces/Interfaces.h"


#define ISS 2000
#define ISC 1000

sc_uint<16> negotiate_mss(sc_uint<16> client_mss) {
        // Use the minimum of client MSS and default MSS
        return ((client_mss < sc_uint<16> (536)) && (client_mss != 0)) ? client_mss : sc_uint<16> (536);
}


SC_MODULE (tcp_server){
    public:
       SC_CTOR(tcp_server){
            SC_THREAD(run);
        }

        enum states {
        CLOSED, SYN_SENT, LISTEN, RST_RCVD, FLUSH, SYN_RCVD, SYN_RCVD_1, ESTABLISHED, ESTABLISHED_1, ABSTRACTED_STATE, FIN_WAIT_1, FIN_WAIT_2, CLOSING, CLOSE_WAIT, LAST_ACK, TIME_WAIT
        };

        states cur_st, nxt_st;

        enum events {
        ACTIVE_OPEN, PASSIVE_OPEN, SEND, RECEIVE_SYN, RECEIVE_RST, RECEIVE_SYN_ACK, RECEIVE_FIN, RECEIVE_FIN_ACK, CLOSE, ABORT, STATUS, SEGMENT_ARRIVES, USER_TIMEOUT, RETRANSMISSION_TIMEOUT, TIME_WAIT_TIMEOUT
        };

        events ev;

        struct TCP_Header{
        sc_uint<16> source_port;
        sc_uint<16> destination_port;
        sc_uint<32> seq_number;
        sc_uint<32> ack_number;
        sc_uint<4> data_offset;
        bool URG;
        bool ACK;
        bool PSH;
        bool RST;
        bool SYN;
        bool FIN;
        sc_uint<16> checksum;
        sc_uint<16> urgent_pointer;
        sc_uint<16> mss; // MSS option (mandatory)
        sc_uint<8> payload[536]; // Payload field with maximum size of MSS (default = 536)
        };

        /*shared_in<TCP_Header> TCP_client_in;
        shared_out<TCP_Header> TCP_server_out;
        shared_in<states> states_in;*/

        shared_in<sc_uint<16>> src_port_in;
        shared_in<sc_uint<16>> dst_port_in;
        shared_in<sc_uint<16>> ctl_loc_port_in;
        shared_in<sc_uint<32>> seq_number_in;
        shared_in<sc_uint<32>> ack_number_in;
        shared_in<sc_uint<32>> pkt_stop_in;
        shared_in<bool> SYN_in;
        shared_in<bool> ACK_in;
        shared_in<bool> FIN_in;
        shared_in<bool> PSH_in;
        shared_in<bool> RST_in;
        shared_in<bool> listen_in;
        shared_in<bool> force_dcn_in;
        blocking_in<bool> ACK_port;
        blocking_in<bool> ACK_port_2;
        blocking_in<bool> ACK_port_3;
        blocking_in<bool> SYN_port;
        blocking_in<bool> SYN_port_2;
        //shared_in<bool> RST;
        //shared_in<sc_uint<16>> mss_in;
        shared_in<sc_uint<32>> tx_ctl_loc_seq_in;
        shared_in<bool> tx_done_in;
        shared_in<bool> tx_eng_acc_in;
        shared_in<sc_uint<32>> last_ack_in;

        shared_out<sc_uint<16>> src_port_out;
        shared_out<sc_uint<16>> dst_port_out;
        shared_out<sc_uint<32>> seq_number_out;
        shared_out<sc_uint<32>> ack_number_out;
        shared_out<bool> SYN_out;
        shared_out<bool> ACK_out;
        shared_out<bool> FIN_out;
        shared_out<bool> RST_out;
        //shared_out<sc_uint<16>> mss_out;

        //TCP_Header t_in, t_out;

        //sc_uint<32> local_seq = ISS;
        sc_uint<32> local_seq, local_ack, remote_ack, remote_seq, seq_number, ack_number, pkt_stop, tx_ctl_loc_seq, last_ack;
        sc_uint<16> local_port, ctl_loc_port;
        sc_uint<16> remote_port, src_port, dst_port, payload_length;
        bool SYN, ACK, FIN, PSH, RST, listen, force_dcn, close, close_active, close_passive, close_reset, tx_done, tx_eng_acc, abstract_port_vld, dcn_send_ack;
        
        // Buffers for incoming and outgoing data
        //sc_uint<8> receive_buffer[536];
        //sc_uint<8> send_buffer[536];

        void run(){

          while(true) {

            //states_in->get(cur_st);

            cur_st = nxt_st;

            if (cur_st == CLOSED) {
              insert_state("CLOSED_S");

              close_reset = false;
              close_active = false;
              close_passive = false;
              RST_out->set(false);
              ACK_out->set(false);
              SYN_out->set(false);
              src_port_out->set(0);
              dst_port_out->set(0);
              ack_number_out->set(0);
              seq_number_out->set(0);
              
              listen_in->get(listen);

              if(listen) {
                nxt_st = LISTEN;
              }
              else {
                nxt_st = CLOSED;
              }              
            }

            else if (cur_st == LISTEN) {
              SYN_port->read(SYN, "LISTEN_S");
              seq_number_in->get(seq_number);
              src_port_in->get(src_port);
              ctl_loc_port_in->get(ctl_loc_port);

              local_seq = 0x7d0; //initial seq number, random value
              local_ack = seq_number + 1;
              remote_port = src_port;
              local_port = ctl_loc_port;

              nxt_st = SYN_RCVD;
            }

            else if (cur_st == SYN_RCVD) {
              insert_state("SYN_RCVD_S");

              src_port_out->set(local_port);
              dst_port_out->set(remote_port);
              SYN_out->set(true);
              ACK_out->set(true);
              RST_out->set(false);
              ack_number_out->set(local_ack); 
              seq_number_out->set(local_seq);

              nxt_st = SYN_RCVD_1;
            }

            else if (cur_st == SYN_RCVD_1) {
              ACK_port_2->read(ACK, "SYN_RCVD_1_S");

              ++local_seq;
              
              nxt_st = ESTABLISHED;
            }


            else if (cur_st == ESTABLISHED) {
              insert_state("ESTABLISHED_S");
              FIN_in->get(FIN);
              RST_in->get(RST);
              src_port_in->get(src_port);
              dst_port_in->get(dst_port);

              tx_ctl_loc_seq_in->get(tx_ctl_loc_seq);
              local_seq = tx_ctl_loc_seq;

              tx_done_in->get(tx_done);
              last_ack_in->get(last_ack);
              
              if (tx_done) {
                local_ack = last_ack;
              }
              listen_in->get(listen);
              force_dcn_in->get(force_dcn);

              if (!listen || force_dcn) {
                close_active = true;
                nxt_st = ESTABLISHED_1;
              }
              else if (FIN && (src_port == remote_port) && (dst_port == local_port)) {
                close_passive = true;
                nxt_st = ESTABLISHED_1;
              }
              else if(RST && (src_port == remote_port) && (dst_port == local_port)) {
                close_reset = true;
                nxt_st = ESTABLISHED_1;
              }
              else {
                nxt_st = ESTABLISHED;
              }
            }
            
            else if (cur_st == ESTABLISHED_1) {
              insert_state("ESTABLISHED_1_S");

              tx_ctl_loc_seq_in->get(tx_ctl_loc_seq);
              local_seq = tx_ctl_loc_seq;

              tx_done_in->get(tx_done);
              last_ack_in->get(last_ack);

              RST_in->get(RST);
              src_port_in->get(src_port);
              dst_port_in->get(dst_port);

              /*if (RST && (src_port == remote_port) && (dst_port == local_port)) {
                close_reset = true;
              }*/
              
              if (tx_done) {
                local_ack = last_ack;
              }

              //nxt_st = ABSTRACTED_STATE;
              nxt_st = FLUSH;
              
            }
            //version 1 (working)
            else if (cur_st == FLUSH) {
              ACK_port_3->read(ACK, "FLUSH_S");

              if (close_reset) {
                nxt_st = RST_RCVD;
              }
              else {
                nxt_st = ABSTRACTED_STATE;
              }
            }
            /*else if (cur_st == ABSTRACTED_STATE) {
              ACK_port->read(ACK, "ABSTRACT_S");

              nxt_st = CLOSED;
            }*/
            //version 2 trying
            /*else if (cur_st == FLUSH) {
              ACK_port_3->read(ACK, "FLUSH_S");

              if (close_reset) {
                nxt_st = RST_RCVD;
              }
              else if (close_active || close_passive) {
                nxt_st = ABSTRACTED_STATE;
              }
              else {
                nxt_st = FLUSH;
              }
            }*/
            else if (cur_st == ABSTRACTED_STATE) {
              insert_state("ABSTRACT_S");

              ACK_out->set(true);
              SYN_out->set(false);
              seq_number_out->set(local_seq);
              //ack_number_out->set(local_ack);
              //added
              if (dcn_send_ack) {
                //FIN_out->set(true);
                ack_number_out->set(local_ack + 1);
                tx_eng_acc_in->get(tx_eng_acc);
                if (tx_eng_acc) {
                  ++local_ack;
                }
                nxt_st = ABSTRACTED_STATE;
              }
              else { 
                ack_number_out->set(local_ack);
                if (abstract_port_vld) {
                  nxt_st = CLOSED;
                }
                else {
                  nxt_st = ABSTRACTED_STATE;
                }
              }
              //done added
              /*if (abstract_port_vld) {
                nxt_st = CLOSED;
              }
              else {
                nxt_st = ABSTRACTED_STATE;
              }*/
            }
            //end version 2
            else if (cur_st == RST_RCVD) {
              insert_state("RST_RCVD_S");

              RST_out->set(true);
              ACK_out->set(true);
              SYN_out->set(false);
              ack_number_out->set(local_ack); 
              seq_number_out->set(local_seq);

              //close_reset = false;

              nxt_st = CLOSED;

              /*tx_eng_acc_in->get(tx_eng_acc);
              if (tx_eng_acc) {
                nxt_st = CLOSED;
              }
              else {
                nxt_st = RST_RCVD;
              }*/
              
            }
  
          }
        }
};
#endif
