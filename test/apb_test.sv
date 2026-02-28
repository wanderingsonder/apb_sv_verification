//`ifndef APB_TEST
//`define APB_TEST
`include "/home/dvft0901/apb_sv_project/test/apb_write_read_test.sv"
`include "/home/dvft0901/apb_sv_project/test/apb_write_test.sv"
`include "/home/dvft0901/apb_sv_project/test/apb_read_test.sv"
`include "/home/dvft0901/apb_sv_project/test/apb_slverr_test.sv"
`include "/home/dvft0901/apb_sv_project/test/apb_reset_test.sv"

`include "/home/dvft0901/apb_sv_project/test/apb_write_read_zerowait_test.sv"
`include "/home/dvft0901/apb_sv_project/test/apb_write_zerowait_test.sv"
`include "/home/dvft0901/apb_sv_project/test/apb_read_zerowait_test.sv"
`include "/home/dvft0901/apb_sv_project/test/apb_slverr_zerowait_test.sv"
`include "/home/dvft0901/apb_sv_project/test/apb_reset_zerowait_test.sv"



class apb_test;
virtual apb_interface vif;
virtual apb_interface dr_vif;
virtual apb_interface mo_vif;
virtual apb_interface reset_vif;
apb_envrionment env;
apb_generator gen;


apb_write_read_test apb_wr_rd;
apb_slverr_test apb_slverr;
apb_write_test apb_wr;
apb_read_test apb_rd;
apb_reset_test apb_rst;

apb_write_read_zerowait_test apb_wr_rd_zw;
apb_slverr_zerowait_test apb_slverr_zw;
apb_write_zerowait_test apb_wr_zw;
apb_read_zerowait_test apb_rd_zw;
apb_reset_zerowait_test apb_rst_zw;


function new(virtual apb_interface dr_vif,virtual apb_interface mo_vif,virtual apb_interface reset_vif);
   this.dr_vif=dr_vif;
   this.mo_vif=mo_vif;
   this.reset_vif=reset_vif;
endfunction 
task build_and_run();
   env=new(dr_vif,mo_vif,reset_vif);
   begin
      if ($test$plusargs("apb_write_read_test")) begin
         $display("time=%0t inside APB_WRITE_READ_TEST",$time);
        apb_wr_rd=new(env.gdmbx);
       env.build();
       env.gen=apb_wr_rd;
       env.run(); 
    end 

      if ($test$plusargs("apb_write_test")) begin
         $display("time=%0t inside APB_WRITE_TEST",$time);
        apb_wr=new(env.gdmbx);
       env.build();
       env.gen=apb_wr;
       env.run(); 
    end

      if ($test$plusargs("apb_read_test")) begin
         $display("time=%0t inside APB_READ_TEST",$time);
        apb_rd=new(env.gdmbx);
       env.build();
       env.gen=apb_rd;
       env.run(); 
    end


      if ($test$plusargs("apb_slverr_test")) begin
         $display("time=%0t inside APB_SLVERR_TEST",$time);
        apb_slverr=new(env.gdmbx);
       env.build();
       env.gen=apb_slverr;
       env.run(); 
    end

     if ($test$plusargs("apb_reset_test")) begin
         $display("time=%0t inside APB_RESET_TEST",$time);
        apb_rst=new(env.gdmbx);
       env.build();
       env.gen=apb_rst;
   fork
#500; reset_vif.rst_n ='0;
#510; reset_vif.rst_n ='0;

#650; reset_vif.rst_n ='0;
#680; reset_vif.rst_n ='0;

#800; reset_vif.rst_n ='0;
#850; reset_vif.rst_n ='0;

#1000; reset_vif.rst_n ='0;
#1050; reset_vif.rst_n ='0;
 join_none
 env.run(); 
 end 

///********* ZERO WAIT TEST ************//

  if ($test$plusargs("apb_write_read_zerowait_test")) begin
         $display("time=%0t inside APB_WRITE_READ_ZEROWAIT_TEST",$time);
        apb_wr_rd_zw=new(env.gdmbx);
       env.build();
       env.gen=apb_wr_rd_zw;
       env.run(); 
    end 


      if ($test$plusargs("apb_write_zerowait_test")) begin
         $display("time=%0t inside APB_WRITE_ZEROWAIT_TEST",$time);
        apb_wr_zw=new(env.gdmbx);
       env.build();
       env.gen=apb_wr_zw;
       env.run(); 
    end


      if ($test$plusargs("apb_read_zerowait_test")) begin
         $display("time=%0t inside APB_READ_ZEROWAIT_TEST",$time);
        apb_rd_zw=new(env.gdmbx);
       env.build();
       env.gen=apb_rd_zw;
       env.run(); 
    end


      if ($test$plusargs("apb_slverr_zerowait_test")) begin
         $display("time=%0t inside APB_SLVERR_ZEROWAIT_TEST",$time);
        apb_slverr_zw=new(env.gdmbx);
       env.build();
       env.gen=apb_slverr_zw;
       env.run(); 
    end

    if ($test$plusargs("apb_reset_zerowait_test")) begin
         $display("time=%0t inside APB_RESET_ZEROWAIT_TEST",$time);
        apb_rst_zw=new(env.gdmbx);
       env.build();
       env.gen=apb_rst_zw;
   fork
#500; reset_vif.rst_n ='0;
#510; reset_vif.rst_n ='0;

#650; reset_vif.rst_n ='0;
#680; reset_vif.rst_n ='0;

#800; reset_vif.rst_n ='0;
#850; reset_vif.rst_n ='0;

#1000; reset_vif.rst_n ='0;
#1050; reset_vif.rst_n ='0;
 join_none
 env.run(); 
 end 

 end
endtask
endclass

      
