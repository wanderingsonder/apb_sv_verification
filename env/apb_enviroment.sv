class apb_envrionment;
apb_generator gen;
apb_driver dvr;
apb_monitor mon;
apb_predictor pre; //new line added
apb_scoreboard sco; // new line for sco

mailbox gdmbx=new(1);
mailbox mpmbx=new();
mailbox msmbx=new();
mailbox psmbx=new(); //new line added pre->sco

virtual apb_interface dr_vif; //interface instance for driver
virtual apb_interface mo_vif; //interface instance for monitor
virtual apb_interface reset_vif; //interface instance for predictor

function new(virtual apb_interface dr_vif,
   virtual apb_interface mo_vif,virtual apb_interface reset_vif);

this.dr_vif=dr_vif;
this.mo_vif=mo_vif;
this.reset_vif=reset_vif;
endfunction

task build();
   gen=new(gdmbx);
   dvr=new(dr_vif,gdmbx);
   mon=new(mo_vif,mpmbx,msmbx);
   pre=new(mo_vif,mpmbx,psmbx); //new line added
   sco=new(msmbx,psmbx); // new line for scoreboard
endtask

task run();
   #20;
   start_process();
endtask

task start_process();
   fork
      gen.run();
      dvr.run();
      mon.run();
      pre.run(); // new line added
      sco.run();// new line for scoreboard
   join_none

endtask
endclass






