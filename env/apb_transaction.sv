//`ifndef APB_TRANSACTION
//`define APB_TRANSACTION

class apb_transaction;
   rand bit [31:0] paddr;
   rand bit [31:0] pwdata;
   rand bit pwrite;

      bit psel;
      bit penable;

      bit [31:0] prdata;
      bit pready;
      bit pslverr;   

constraint addr_c{soft paddr inside  {8'hff,8'h55,8'hcc,8'hab,8'hfc,8'hbe,8'hfa,8'haf,8'hf5,8'hcd,8'h5c,8'ha2};} 

constraint addr_a {!paddr inside {0,4,8,12};}

constraint data_c {soft pwdata inside {8'h55,8'h50,8'h54,

                                           32'hFFFF_FFFF,
                                           32'hAAAA_AAAA,
                                           32'h5555_5555,
                                           32'hA5A5_A5A5,
                                           32'h5A5A_5A5A,
                                           32'hF5F5_F5F5,
   32'hAFAF_AFAF,
   32'hABAB_ABAB,
   32'h5353_5353,
   32'hABCD_EFAB,
   32'h1234_5A5A,
   32'h7894_F5F5,
   32'hACAD_ACAD,
   32'hACAF_ACAF,
   32'h5151_5656,
   32'hEF67_EF67,
   32'hCC34_DD5A,
   32'h7788_99F5};}
constraint pwrite_c {soft pwrite inside{0,1};}

function void display(input string tag);
$display("[%0s] : [%0t] paddr: %0h | pwdata: %0h | prdata: %0h | pwrite : %0b | psel: %0b | penable :%0b | pready: %0b | pslverr: %0b",tag,
   $time,paddr,pwdata,prdata,pwrite,psel,penable,pready,pslverr);
endfunction
endclass : apb_transaction
//`endif

