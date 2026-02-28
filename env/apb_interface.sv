// `ifndef APB_INTERFACE
// `define APB_INTERFACE

interface apb_interface;
 logic rst_n;
 logic pclk;
 logic psel;
 logic penable;
 logic pwrite;
 logic [31:0] paddr;
 logic [31:0] pwdata;
 logic [31:0] prdata;
 logic pready,pslverr;
 

 clocking dr_cb @(posedge pclk);
   output psel,pwrite,pwdata,paddr,penable;
   input pready,prdata,pslverr;
endclocking

clocking mo_cb @(posedge pclk);
input psel,pwrite,pwdata,paddr,penable,prdata,pready,pslverr;
endclocking

modport dr_mp(clocking dr_cb);
modport mo_mp(clocking mo_cb);


property pready_check;
@(posedge pclk) $rose(psel) ##1 penable |-> ##[0:5] pready;
endproperty

assertion_check: assert property(pready_check); 
endinterface 

//`endif


