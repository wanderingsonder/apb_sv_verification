class apb_predictor;

apb_transaction mppkt;
apb_transaction pspkt;
virtual apb_interface reset_vif;
bit [31:0] mem [256];

mailbox mpmbx;
mailbox psmbx;

function new (virtual apb_interface reset_vif, mailbox mpmbx, mailbox psmbx);
   this.reset_vif=reset_vif;
   this.mpmbx=mpmbx;
   this.psmbx=psmbx;
endfunction

task run ();
   pspkt = new();
   forever begin
      if (reset_vif.rst_n==0) begin 

         pspkt.prdata <=0;// orignal line
         //$display("PRE => RESET DONE ");
         pspkt.pready <=1;
         for (int i=0; i<256; i++) mem[i]=i;
         @(posedge reset_vif.pclk);
   end 
   else begin
      mpmbx.get(mppkt);
      if (mppkt.pslverr) begin
         pspkt.pslverr=mppkt.pslverr;
         pspkt.prdata=mppkt.prdata;
         pspkt.pready=mppkt.pready;
         pspkt.paddr=mppkt.paddr;
         pspkt.psel=mppkt.psel;
         pspkt.pwrite=mppkt.pwrite;
         $display("[SLV ERROR] INVALID ADDRESS LOCATION IS %0d",mppkt.paddr);
      end

      else begin
         if(mppkt.pwrite) begin
            mem[mppkt.paddr]=mppkt.pwdata;
            pspkt.paddr=mppkt.paddr;
            pspkt.pwdata=mppkt.pwdata;
            pspkt.prdata=mppkt.prdata;
            pspkt.pslverr=mppkt.pslverr;
            pspkt.pready=mppkt.pready;
            pspkt.psel=mppkt.psel;
            pspkt.pwrite=mppkt.pwrite;
         
            // $display("[PRE] Writing mem[%0h] = %h",mppkt.paddr,mppkt.pwdata);
         end

         else begin
         
            pspkt.paddr=mppkt.paddr;
            pspkt.pwdata=0;
            pspkt.prdata=mppkt.prdata;
            pspkt.pslverr=mppkt.pslverr;
            pspkt.pready=mppkt.pready;
            pspkt.psel=mppkt.psel;
            pspkt.pwrite=mppkt.pwrite;
            pspkt.prdata=mem[mppkt.paddr];
            // $display("[PRE] Reading mem[%0h] = %h",mppkt.paddr,mem[mppkt.paddr);
         end
      end

      psmbx.put(pspkt);
      pspkt.display("PRE");
   end
end
endtask
endclass
      


         









