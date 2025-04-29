// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 22.02.2025 at 10:07                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


#ifndef TCP_SERVER_TESTS_H
#define TCP_SERVER_TESTS_H


#include "systemc.h"
#include "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/tcp_server.h"
#include "/home/muhammad-haekal/.vscode-server/extensions/lubis-eda.lubis-vsc-plugin-1.0.0/DeSCAM/include/interfaces/Interfaces.h"


SC_MODULE(tcp_server_tests) {
public:
  SC_CTOR(tcp_server_tests) {
    SC_THREAD(run);
  }

  shared_out<tcp_server::TCP_Header> TCP_client_in;
  shared_in<tcp_server::TCP_Header> TCP_server_out;

  shared_out<tcp_server::states> states_in;

  tcp_server::TCP_Header t_in, t_out;

  void run() {

    
    states_in->set(tcp_server::states::LISTEN);
    
    t_out.SYN = true;
    t_out.ACK = false;
    t_out.seq_number = 100;
    t_out.mss = 0;
    TCP_client_in->set(t_out);
    
    
    /*states_in->set(tcp_server::states::ESTABLISHED);

    t_out.PSH = true;
    t_out.seq_number = 101;
    t_out.mss = 300;
    TCP_client_in->set(t_out);

    */

      
  }
};


#endif
