class apb_reset_test extends apb_generator;
apb_transaction tr;
bit pclk;
bit rst_n;
function new(mailbox gdmbx);
         super.new(gdmbx);
      endfunction
task run();
for (int i=1; i<21; i=i+1)begin
 tr =new();

 if (i<11) begin 
tr.randomize() with {pwrite== 1;}; end //write

else begin tr.randomize() with {pwrite== 0; pwdata==0;}; end //read
 gdmbx.put(tr);
$display("*************************************************");
 tr.display ("GEN");
 gdmbx.put(tr);
 @(e1);
 #1;
end
 endtask : run
 endclass

