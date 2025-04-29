property SDA_constraints_p;
   (master_I2C.SDA_tx == 1'd1)
|->
    sda_in == 1'd1 ||
    sda_in == 1'd0;
endproperty
run_SDA_constraints_a: assume property (disable iff(rst) SDA_constraints_p);

property num_bytes_send_p;
   master_I2C.num_bytes_send == 'h3 &&
   master_I2C.num_bytes_receive == 'h3;
endproperty
num_bytes_send_a: assume property (disable iff(rst) num_bytes_send_p);

property stable_addr_p;
   $stable(master_I2C.addr_target) &&
   $stable(master_I2C.data_send);
endproperty
stable_addr_a: assume property (disable iff(rst) stable_addr_p);

property SDA_constraints_p;
   (i2c_controller.sda_out == 1'd1)
|->
    sda_in == 1'd1 ||
    sda_in == 1'd0;
endproperty
run_SDA_constraints_a: assume property (disable iff(rst) SDA_constraints_p);


property stable_addr_p;
   $stable(i2c_controller.addr) &&
   $stable(i2c_controller.data_snt);
endproperty
stable_addr_a: assume property (disable iff(rst) stable_addr_p);