// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 29.04.2025 at 10:34                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package tcp_server_functions;


function logic unsigned [15:0] negotiate_mss(logic unsigned [15:0] client_mss);
  return ((client_mss < 16'd536) && (client_mss != 64'd0)) ? client_mss : 16'd536;
endfunction


endpackage
