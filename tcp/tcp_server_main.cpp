// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 22.02.2025 at 10:07                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


#include "systemc.h"
#include "/home/muhammad-haekal/.vscode-server/extensions/lubis-eda.lubis-vsc-plugin-1.0.0/DeSCAM/include/interfaces/Interfaces.h"
#include "/home/muhammad-haekal/Documents/esl_bootcamp/esl_bootcamp_up/thesis/tcp/tcp_server.h"
#include "tcp_server_tests.h"


int sc_main(int argc, char **argv) {
  tcp_server dut("dut");
  tcp_server_tests tests("tests");

  Shared<tcp_server::TCP_Header> TCP_client_in_channel("TCP_client_in_channel");
  Shared<tcp_server::TCP_Header> TCP_server_out_channel("TCP_server_out_channel");
  Shared<tcp_server::states> states_in_channel("states_in_channel");
  

  dut.TCP_client_in(TCP_client_in_channel);
  dut.TCP_server_out(TCP_server_out_channel);
  dut.states_in(states_in_channel); // Bind to server

  tests.TCP_client_in(TCP_client_in_channel);
  tests.TCP_server_out(TCP_server_out_channel);
  tests.states_in(states_in_channel); // Bind to testbench

  sc_start();
  return 0;
}
