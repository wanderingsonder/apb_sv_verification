class apb_scoreboard;

mailbox msmbx;
mailbox psmbx;

apb_transaction mon2sco; //  from monitor
apb_transaction pre2sco; //  from predictor

apb_predictor m_pre;

covergroup apb_cov1;

CP1: coverpoint pre2sco.paddr  {bins b1={[0:127]}; bins b2={32'hFFFF_FFFF};} 
CP2: coverpoint pre2sco.pwdata {bins b3={[0:255]};} 
CP3: coverpoint pre2sco.prdata {bins b4={[0:255]};} 
CP4: coverpoint pre2sco.psel   {bins psel_one={1};} //bins psel_zero={0};}  
CP5: coverpoint pre2sco.pwrite {bins pwrite_1={1}; bins pwrite_0={0};}
CP6: coverpoint pre2sco.pslverr {bins pslverr_1={1}; bins pslverr_0={0};}

CP2_X_CP5: cross CP2, CP5;
CP3_X_CP5: cross CP3, CP5;

endgroup: apb_cov1

   
function new (mailbox msmbx, mailbox psmbx);

   this.msmbx=msmbx;
   this.psmbx=psmbx;
   apb_cov1=new();
endfunction

task run();
   forever begin
   msmbx.get(mon2sco);
   psmbx.get(pre2sco);

   apb_cov1.sample();

   if(mon2sco.pwrite==1'b0) begin
      if(mon2sco.prdata == pre2sco.prdata)
         $display("[SCO] TIME =%0t, PASS=PRDATA mon=%0h<=>%0h=pre",
      $time,mon2sco.prdata,pre2sco.prdata); 

      else  $display("[SCO] TIME = %0t, FAIL = PRDATA mon=%0h<=>%0h=pre",
         $time,mon2sco.prdata,pre2sco.prdata); 


      end
   end

endtask
endclass








/*function new(mailbox msmbx, mailbox psmbx);
   this.msmbx=msmbx;
   this.psmbx=psmbx;
endfunction

task run();
   forever begin 
   // pair up predicted and monitored items
   fork
      psmbx.get(ps);
      msmbx.get(ms);
   join
   compare();
end
endtask

task compare();
   // compare only for READS; 
   // For writes the predictor just updates its model
   if(ms.pslverr != ps.pslverr)
   begin
         $display("[SCO] [FAIL] PSLVERR MISMATCH -> MON saw: %b, PRE predicted: %b at [ADDR=%0h]",ms.pslverr,ps.pslverr,ms.paddr);end
         else if (ms.pwrite == 1'b0 && ms.pslverr==1'b0) begin
            if (ms.prdata==ps.prdata)
         $display("[SCO] [PASS] ms.prdata %0h <=> %0h ps.rdata",ms.prdata,ps.prdata);
               
            else
             $display("[SCO] [FAIL] ms.prdata %0h <=> %0h ps.rdata at [ADDR=%0h]",ms.prdata,ps.prdata,ps.paddr);end  
         
      endtask
   endclass */





 /*  if (ms.pwrite==1'b0 && ms.pslverr==1'b0) begin //&& part to get all pass valued
      if(ms.prdata==ps.prdata)
         $display("[SCO] [PASS] ms.prdata %0h <=> %0h ps.rdata",ms.prdata,ps.prdata);end


      else begin
         $display("[SCO] [FAIL] ms.prdata %0h <=> %0h ps.rdata at [ADDR=%0h]",ms.prdata,ps.prdata,ps.paddr);end       
endtask
endclass */


