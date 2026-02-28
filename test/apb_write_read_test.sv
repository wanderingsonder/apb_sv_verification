class apb_write_read_test extends apb_generator;
apb_transaction tr;

function new(mailbox gdmbx);
         super.new(gdmbx);
      endfunction

  task run(); 
   for (int i=1; i<21; i=i+1)begin
 tr =new();

 if (i<11) begin 
assert(tr.randomize() with {tr.pwrite== 1'b1;}); end //write

else begin assert(tr.randomize() with {tr.pwrite== 1'b0; tr.pwdata=='h0;}); end //read
$display("*************************************************");
 tr.display ("GEN");
 gdmbx.put(tr);
 @(e1);
 #1;
 end
 endtask : run
 endclass


