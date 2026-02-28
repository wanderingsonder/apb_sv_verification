// `ifndef APB_MONITOR
// `define APB_MONITOR

class apb_monitor;

virtual apb_interface vif;

mailbox mpmbx;
mailbox msmbx;
apb_transaction tr;

function new(virtual apb_interface vif, mailbox mpmbx, mailbox msmbx);
   this.vif=vif;
   this.mpmbx=mpmbx;
   this.msmbx=msmbx;
endfunction

task run();
    if ($test$plusargs("zerowaitstate")) zero_wait_logic();
      else with_wait_logic();
          endtask

task with_wait_logic();
   tr=new();
   forever begin
   @(vif.mo_cb) begin
      if ((vif.mo_cb.psel)&&(!vif.mo_cb.penable)) begin
         @(vif.mo_cb);
         if (vif.mo_cb.psel && vif.mo_cb.penable) begin
            wait (vif.mo_cb.pready);
            tr.pwdata = vif.pwdata;
            tr.paddr = vif.paddr;
            tr.pwrite = vif.pwrite;
            tr.psel = vif.psel;
            tr.penable = vif.penable;
            tr.pready = vif.pready;
            tr.prdata = vif.prdata;
            tr.pslverr = vif.pslverr;
            tr.display("MON");
         end
         mpmbx.put(tr);
         msmbx.put(tr);
         ->e1;
      end
   end
end
endtask



task zero_wait_logic();
   tr=new();
   forever begin
   @(vif.mo_cb) begin
      if ((vif.mo_cb.psel)&&(!vif.mo_cb.penable)) begin
         @(vif.mo_cb);
         if (vif.mo_cb.psel && vif.mo_cb.penable) begin
            tr.pwdata = vif.pwdata;
            tr.paddr = vif.paddr;
            tr.pwrite = vif.pwrite;
            tr.psel = vif.psel;
            tr.penable = vif.penable;
            tr.pready = vif.pready;
            tr.prdata = vif.prdata;
            tr.pslverr = vif.pslverr;
         end
            tr.display("MON");
            $display("****************************************************************");
         mpmbx.put(tr);
         msmbx.put(tr);
         ->e1;
      end
   end
end
endtask
endclass




