module apb_top;

import apb_pkg::*;

bit pclk,rst_n;

apb_interface vif();  
apb_test test_h;
apb_slave DUT(.dif(vif));
always #5 vif.pclk = ~vif.pclk;

initial begin
   vif.pclk=0;
   vif.rst_n=1'b0;
   #40;
   vif.rst_n=1'b1;
end

initial begin
   test_h =new(vif,vif,vif);
   test_h.build_and_run(); 
   #1800 $finish;
end
endmodule

