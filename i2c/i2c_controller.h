#ifndef _I2C_CONTROLLER_
#define _I2C_CONTROLLER_

#include "systemc.h"
#include "/home/muhammad-haekal/.vscode-server/extensions/lubis-eda.lubis-vsc-plugin-1.0.0/DeSCAM/include/interfaces/Interfaces.h"


#define TSU_DAT 100
#define THD_STA 225
#define TSU_STO 225
#define TLOW 250
#define THIGH 225
#define THIGH_SAMPLE 50
#define TBUF 250
#define BYTES_TO_BE_SENT 3 //# bytes of data controller is sending
#define BYTES_TO_BE_RCVD 3 //# bytes of data controller is receiving


SC_MODULE (i2c_controller){
    public:
       SC_CTOR(i2c_controller){
            SC_THREAD(run);
        }
        enum states {
            IDLE, START, LOW_CLK_ADDR, HIGH_CLK_ADDR, LOW_ADDR_ACK, HIGH_ADDR_ACK, LOW_CLK_DATA, HIGH_CLK_DATA, 
            LOW_DATA_ACK, HIGH_DATA_ACK, LOW_STOP, HIGH_STOP
        };

        states cur_st, nxt_st;

        shared_in<sc_uint<1>> start;
        shared_out<sc_uint<1>> scl;
        shared_out<sc_uint<1>> sda_out;
        shared_in<sc_uint<1>> sda_in;
        shared_in<sc_uint<8>> addr;
        shared_in<sc_uint<8*BYTES_TO_BE_SENT>> data_snt;
        shared_out<sc_uint<8*BYTES_TO_BE_RCVD>> data_rcv;
        shared_in<sc_uint<8*BYTES_TO_BE_RCVD>> data_rcv_in;
        

        sc_uint<1> s;
        sc_uint<4> bit_count_data, bit_count_addr;
        sc_uint<2> sent_byte, rcvd_byte;
        sc_uint<8> addr_shift_reg;
        sc_uint<10> count_thd, count_tlow, count_thigh;
        sc_uint<8*BYTES_TO_BE_SENT> data_shift_reg;
        sc_uint<8*BYTES_TO_BE_RCVD> data, data_out;
        sc_uint<1> scl_en, sda_en, ack, sda_data, rw;
        sc_uint<8> a;
        sc_uint<8*BYTES_TO_BE_SENT> d;



        void run() {

            while(true) {

                cur_st = nxt_st;
                if (cur_st == IDLE) {

                    //RESET COND
                    sda_out->set(1);
                    scl->set(1);

                    insert_state("IDLE_S");
                    data_rcv->set(0);
                    sda_out->set(1);
                    rw = 0;
                    bit_count_addr = 0;
                    bit_count_data = 0;
                    sent_byte = 0;
                    rcvd_byte = 0;
                    count_thd = 0;
                    count_thigh = 0; //added because IDLE to IDLE is failing
                    start->get(s);

                    if (s) {
                        count_thd = 0;
                        nxt_st = START;
                    }
                    else {
                        nxt_st = IDLE;
                    }
                }
                else if (cur_st == START) {
                    insert_state("START_S");
                    sda_out->set(0);
                    scl->set(1);
                    addr->get(a);
                    data_snt->get(d);
                    sent_byte = 0;
                    rcvd_byte = 0;
                    addr_shift_reg = a;
                    data_shift_reg = d;
                    rw = a[0];

                    if (count_thd < THD_STA) { //SCL line wil stay high until THD_STA time elapsed.
                        ++count_thd;
                        //scl->set(1);
                        nxt_st = START;
                    }
                    else {
                        bit_count_addr = 0;
                        count_tlow = 0;
                        ++count_thd;
                        nxt_st = LOW_CLK_ADDR;
                    }
                }
                else if (cur_st == LOW_CLK_ADDR) {
                    insert_state("LOW_CLK_ADDR_S");
                    //scl->set(0);
                    count_thigh = 0;

                    if (count_tlow < TLOW) {
                        scl->set(0);
                        if (count_tlow == (TLOW-TSU_DAT)) {  
                            //Data must be stable for TSU DAT time before rising edge of next SCL
                            sda_out->set(sc_uint<1> (addr_shift_reg[7]));
                            addr_shift_reg = addr_shift_reg << 1;
                            ++bit_count_addr;
                        }
                        ++count_tlow;
                        nxt_st = LOW_CLK_ADDR;
                    }
                    else {
                        scl->set(1);
                        //count_thigh = 0;
                        nxt_st = HIGH_CLK_ADDR;
                    }
                }
                else if (cur_st == HIGH_CLK_ADDR) {
                    insert_state("HIGH_CLK_ADDR_S");
                    scl->set(1);
                    count_tlow = 0;

                    if (count_thigh < THIGH) {
                        //++count_thigh;
                        nxt_st = HIGH_CLK_ADDR;
                    }
                    else if (bit_count_addr < 8) {
                        nxt_st = LOW_CLK_ADDR;
                    }
                    else {
                        nxt_st = LOW_ADDR_ACK;
                    }
                    ++count_thigh;
                }
                else if (cur_st == LOW_ADDR_ACK) {
                    insert_state("LOW_ADDR_ACK_S");
                    //scl->set(0);
                    sda_out->set(1); //set logic to high to enable read on SDA line
                    count_thigh = 0;

                    if (count_tlow < TLOW) {
                        ++count_tlow;
                        scl->set(0);
                        nxt_st = LOW_ADDR_ACK;
                    }
                    else {
                        scl->set(1);
                        //count_thigh = 0;
                        nxt_st = HIGH_ADDR_ACK;
                    }
                }
                else if (cur_st == HIGH_ADDR_ACK) {
                    insert_state("HIGH_ADDR_ACK_S");
                    scl->set(1);
                    count_tlow = 0;

                    if (count_thigh < THIGH) {

                        if (count_thigh == THIGH_SAMPLE) {
                            sda_in->get(ack);
                        }
                        //++count_thigh;
                        nxt_st = HIGH_ADDR_ACK;
                    }
                    else {
                        //count_tlow = 0;
                        bit_count_data = 0;
                        nxt_st = LOW_CLK_DATA;
                    }
                    ++count_thigh;
                }
                else if (cur_st == LOW_CLK_DATA) {
                    insert_state("LOW_CLK_DATA_S");
                    count_thigh = 0;
                    if (ack) {
                        scl->set(0);
                        ++count_tlow;
                        nxt_st = LOW_STOP; //if NACK, go to STOP
                    }
                    else {
                        //scl->set(0);

                        if (count_tlow < TLOW) {
                            if ((count_tlow == (TLOW-TSU_DAT)) && !rw) {  //if wr == 0, write data to SDA
                                sda_out->set(sc_uint<1> (data_shift_reg[8*BYTES_TO_BE_SENT-1]));
                                data_shift_reg = data_shift_reg << 1;
                                ++bit_count_data;
                            }
                            else if (rw == 1) {
                                sda_out->set(1); //release line when read mode to receive data from target.
                            }
                            scl->set(0);
                            ++count_tlow;
                            nxt_st = LOW_CLK_DATA;
                        }
                        else {
                            scl->set(1);
                            //count_thigh = 0;
                            nxt_st = HIGH_CLK_DATA;
                        }
                    }                   
                }
                else if (cur_st == HIGH_CLK_DATA) {
                    insert_state("HIGH_CLK_DATA_S");
                    scl->set(1);
                    count_tlow = 0;

                    if (count_thigh < THIGH) {

                        if (count_thigh == THIGH_SAMPLE && rw) {
                            sda_in->get(sda_data);
                            //data_shift_reg = {data_shift_reg.range(8*BYTES_TO_BE_RCVD-2,0), int (sda_data)};
                            data_rcv_in->get(data);
                            data_out = (sc_uint<24> (data << 1) | sc_uint<24> (sda_data));
                            data_rcv->set(data_out);
                            ++bit_count_data;
                        }
                        //++count_thigh;
                        nxt_st = HIGH_CLK_DATA;
                    }
                    else if (bit_count_data < 8) {
                        nxt_st = LOW_CLK_DATA;
                    }
                    else {
                        nxt_st = LOW_DATA_ACK;
                    }
                    ++count_thigh;
                }
                else if (cur_st == LOW_DATA_ACK) {
                    insert_state("LOW_DATA_ACK_S");
                    count_thigh = 0;
                    
                    if (count_tlow < TLOW) {
                        scl->set(0);

                        if ((count_tlow == (TLOW-TSU_DAT)) && (rw == 1)) {  //if rw == 1 (read), write ack/nack to SDA
                            ++rcvd_byte;
                            if (rcvd_byte != (BYTES_TO_BE_RCVD)) { //if number of bytes to be read is still > 0, ACK CASE
                                sda_out->set(0);
                            }
                            else {
                                sda_out->set(1); //else, NACK CASE
                            }  
                        }
                        else if (rw == 0) {
                            sda_out->set(1); //release line when write mode to receive ACK from target.
                        }
                        ++count_tlow;
                        nxt_st = LOW_DATA_ACK;
                    }
                    else {
                        scl->set(1);
                        //count_thigh = 0;
                        nxt_st = HIGH_DATA_ACK;
                    }
                }
                else if (cur_st == HIGH_DATA_ACK) {
                    insert_state("HIGH_DATA_ACK_S");
                    scl->set(1);
                    count_tlow = 0;

                    if (count_thigh < THIGH) {

                        if (count_thigh == THIGH_SAMPLE && !rw) { //if rw = 0 (write), read ack from target.
                            sda_in->get(ack);
                            ++sent_byte;
                        }

                        bit_count_data = 0;
                        //++count_thigh;
                        nxt_st = HIGH_DATA_ACK;
                    }
                    else if (((rw == 1) && (rcvd_byte == BYTES_TO_BE_RCVD)) || (!rw && (sent_byte == BYTES_TO_BE_SENT))) { 
                        // if read mode and no more byte expected or write mode and no more bytes to sent, go to STOP
                        nxt_st = LOW_STOP;
                    }
                    else { //go back to LOW CLK DATA to check for ack.
                        //count_tlow = 0;
                        nxt_st = LOW_CLK_DATA;
                    }
                    ++count_thigh;
                }
                else if (cur_st == LOW_STOP) {
                    insert_state("LOW_STOP_S");
                    count_thigh = 0;
                    
                    if (count_tlow < TLOW) {
                        scl->set(0);

                        if (count_tlow == TLOW-TSU_DAT) {
                            sda_out->set(0); //set sda to low because it was in NACK (high condition) before
                        }
                        ++count_tlow;
                        nxt_st = LOW_STOP;
                    }
                    
                    else {
                        scl->set(1);
                        //count_thigh = 0;
                        nxt_st = HIGH_STOP;
                    }
                }
                else if (cur_st == HIGH_STOP) {
                    insert_state("HIGH_STOP_S");
                    scl->set(1);
                    count_tlow = 0;

                    if (count_thigh < THIGH) {

                        if (count_thigh == TSU_STO) {
                            sda_out->set(1); //set sda to 1 to create the STOP condition, but must be stable min TSU_STO time
                        }
                        //++count_thigh;
                        nxt_st = HIGH_STOP;
                    }
                    
                    else {
                        sda_out->set(1);
                        nxt_st = IDLE;
                    }
                    ++count_thigh;
                }
                else {
                    nxt_st = IDLE;
                }
            }

        }
    };

    #endif