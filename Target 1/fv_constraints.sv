property set_prescale;
    uart_tx.prescale == 1'b1;
endproperty
assume_set_prescale: assume property (disable iff(rst) set_prescale);

property no_valid_while_busy;
    uart_tx.busy
    |->
    !uart_tx.s_axis_tvalid;
endproperty
assume_no_valid_while_busy: assume property (disable iff(rst) no_valid_while_busy); //to not have a valid signal during busy 
//so that from transmit stop bit will transition to idle

property stable_while_valid;
    uart_tx.s_axis_tvalid 
    ##1 !uart_tx.s_axis_tvalid[*64]
    |->
    $stable(uart_tx.s_axis_tdata);
endproperty
assume_stable_while_valid: assume property (disable iff(rst) stable_while_valid);