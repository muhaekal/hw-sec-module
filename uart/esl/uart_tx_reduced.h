
#ifndef _UART_TX
#define _UART_TX

#include "systemc.h"
#include "Interfaces.h"

#define DATA_WIDTH 8
#define PRESCALE 1


SC_MODULE (uart_tx_reduced){
    public:
       SC_CTOR(uart_tx_reduced){
            SC_THREAD(run);
        }

        blocking_in<sc_uint<8>> t_data_port;
        //shared_in<sc_uint<4>> current_cnt;
        //shared_out<sc_uint<4>> cnt_new;
        shared_out<sc_uint<1>> txd_port;
        shared_out<bool> tready_port;
        shared_out<bool> busy_port;
        
        
        sc_uint<8> t_data;
        //sc_uint<4> cnt;
        

        void run(){

          while(true) {

            txd_port->set(1);
            busy_port->set(false);

            tready_port->set(true);

            t_data_port->read(t_data,"IDLE");

            txd_port->set(0);
            busy_port->set(true);
            
            tready_port->set(false);

            insert_state("TRANSMIT_START");

            txd_port->set(1);
            busy_port->set(true);
            
            tready_port->set(false);

            insert_state("TRANSMIT_STOP");


          }
        }
};
#endif
