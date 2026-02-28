//`ifndef APB_DRIVER
// `define APB_DRIVER

class apb_driver;
virtual apb_interface vif;
 apb_transaction tr;
 apb_generator gen;
mailbox gdmbx;

function new(virtual apb_interface vif, mailbox gdmbx);
   this.vif=vif;
   this.gdmbx=gdmbx;
endfunction
task run();
 if ($test$plusargs("zerowaitstate")) zero_wait_logic();
 else with_wait_logic();
endtask

 task with_wait_logic();
    forever begin
      gdmbx.get(tr);
     @(vif.dr_cb);
    vif.dr_cb.psel <=0; // idle state
    vif.dr_cb.penable <=0;

     @(vif.dr_cb);
    vif.dr_cb.psel<=1; //setup state
     vif.dr_cb.penable<=0;
      vif.dr_cb.pwrite<=tr.pwrite;
       vif.dr_cb.pwdata<=tr.pwdata;
        vif.dr_cb.paddr<=tr.paddr;
         
        @(vif.dr_cb);
        vif.dr_cb.penable <= 1; // access state

        tr.display("DRI");

        wait(vif.dr_cb.pready);
     end
  endtask

task zero_wait_logic();
    forever begin
      gdmbx.get(tr);
     @(vif.dr_cb);
    vif.dr_cb.psel <=0; // idle state
    vif.dr_cb.penable <=0;

     @(vif.dr_cb);
    vif.dr_cb.psel<=1; //setup state
     vif.dr_cb.penable<=0;
      vif.dr_cb.pwrite<=tr.pwrite;
       vif.dr_cb.pwdata<=tr.pwdata;
        vif.dr_cb.paddr<=tr.paddr;
         
        @(vif.dr_cb);
        vif.dr_cb.penable <= 1; // access state

        tr.display("DRI");

      //  wait(vif.dr_cb.pready);
     end
  endtask 
  endclass
//  `endif
