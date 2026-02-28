class apb_write_test extends apb_generator;
apb_transaction tr;

function new(mailbox gdmbx);
         super.new(gdmbx);
      endfunction
  task run(); 
   for (int i=1; i<21; i=i+1)begin
 tr =new();
tr.randomize() with {tr.pwrite== 1'b1;};  //write
$display("*************************************************");
 tr.display ("GEN");
 gdmbx.put(tr);
 @(e1);
 #1;
 end
 endtask
 endclass

