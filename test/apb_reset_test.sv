class apb_reset_test extends apb_generator;

apb_transaction tr;

function new(mailbox gdmbx);
   super.new(gdmbx);
endfunction


task run();

  for (int i = 1; i <= 10; i++) begin

   tr = new();

   // First half writes
   if (i <= 10) begin
      assert(tr.randomize() with { pwrite == 1; });
   end

   // Second half reads
   else begin
      assert(tr.randomize() with { pwrite == 0; pwdata == 0; });
   end

   gdmbx.put(tr);

   $display("*************************************************");
   tr.display("GEN");

   @(e1);
   #1;

end

endtask

endclass
