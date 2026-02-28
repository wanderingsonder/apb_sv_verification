//`ifndef APB_GENERATOR
//`define APB_GENERATOR

class apb_generator;

 apb_transaction tr;
 mailbox gdmbx;

 function new (mailbox gdmbx);
    this.gdmbx=gdmbx;
 endfunction 

 virtual task run(); //new line
//comment out below lines

     /*for (int i=1; i<21; i=i+1)begin
 tr =new();

 if (i<11) begin 
tr.randomize() with {tr.pwrite== 1'b1;}; end //write

else begin tr.randomize() with {tr.pwrite== 1'b0; tr.pwdata=='h0;}; end //read
 gdmbx.put(tr);
$display("*************************************************");
 tr.display ("GEN");
 @e1;
 end*/
 endtask : run
 endclass : apb_generator
// `endif


