// Hold raw TCP data to be transmitted, free space when ack received
// The logic here resembles a FIFO, but:
// 1. Read address is an input rather then an automatically incremented value
// 2. Space is freed by incrementing 'ack' input
// 
module tcp_vlg_tx_buf
  import
    ipv4_vlg_pkg::*,
    mac_vlg_pkg::*,
    tcp_vlg_pkg::*,
    eth_vlg_pkg::*;
#(
  parameter D = 16,
  parameter W = 8
)
(
  input  logic         rst,
  input  logic         clk,
  
  input  logic         write,
  input  logic [W-1:0] data_in,

  input  logic [D-1:0] addr, // address to read from 
  output logic [W-1:0] data_out,

  input  tcp_num_t     seq,
  input  tcp_num_t     ack,

  output logic         f,
  output logic         e
);

logic [D-1:0] ptr, space;
assign ptr = seq[D-1:0];

logic [32:0] dif;

assign dif = seq - ack; // remote ack is always < local seq
assign space = (dif[D]) ? 0 : ~dif[D-1:0]; // overflow condition accounted
assign e = (dif == 0);
assign f = (space[D-1:1] == {(D-1){1'b0}}); // space =< 1

reg [W-1:0] mem[(1<<D)-1:0];

always_ff @ (posedge clk) data_out <= mem[addr];

always_ff @ (posedge clk) if (write) mem[ptr] <= data_in;

endmodule : tcp_vlg_tx_buf