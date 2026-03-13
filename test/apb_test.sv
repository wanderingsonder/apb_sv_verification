class apb_test;

//--------------------------------
// Virtual interfaces
//--------------------------------
virtual apb_interface dr_vif;
virtual apb_interface mo_vif;
virtual apb_interface reset_vif;


//--------------------------------
// Environment
//--------------------------------
apb_environment env;


//--------------------------------
// Normal test objects
//--------------------------------
apb_write_test apb_wr;
apb_read_test apb_rd;
apb_write_read_test apb_wr_rd;
apb_reset_test apb_rst;


//--------------------------------
// Zero wait test objects
//--------------------------------
apb_write_zerowait_test apb_wr_zw;
apb_read_zerowait_test apb_rd_zw;
apb_write_read_zerowait_test apb_wr_rd_zw;
apb_reset_zerowait_test apb_rst_zw;


//--------------------------------
// Constructor
//--------------------------------
function new(
    virtual apb_interface dr_vif,
    virtual apb_interface mo_vif,
    virtual apb_interface reset_vif
);

    this.dr_vif = dr_vif;
    this.mo_vif = mo_vif;
    this.reset_vif = reset_vif;

endfunction



//--------------------------------
// Build and Run
//--------------------------------
task build_and_run();

env = new(dr_vif, mo_vif, reset_vif);


//--------------------------------
// WRITE TEST
//--------------------------------
if ($test$plusargs("apb_write_test")) begin

    $display("Running APB WRITE TEST");

    apb_wr = new(env.gdmbx);

    env.build();
    env.gen = apb_wr;

    env.run();

end



//--------------------------------
// READ TEST
//--------------------------------
if ($test$plusargs("apb_read_test")) begin

    $display("Running APB READ TEST");

    apb_rd = new(env.gdmbx);

    env.build();
    env.gen = apb_rd;

    env.run();

end



//--------------------------------
// WRITE READ TEST
//--------------------------------
if ($test$plusargs("apb_write_read_test")) begin

    $display("Running APB WRITE READ TEST");

    apb_wr_rd = new(env.gdmbx);

    env.build();
    env.gen = apb_wr_rd;

    env.run();

end



//--------------------------------
// RESET TEST
//--------------------------------
if ($test$plusargs("apb_reset_test")) begin

    $display("Running APB RESET TEST");

    apb_rst = new(env.gdmbx);

    env.build();
    env.gen = apb_rst;

    fork

        begin
            #500 reset_vif.rst_n = 0;
            #20  reset_vif.rst_n = 1;
        end

        begin
            #800 reset_vif.rst_n = 0;
            #20  reset_vif.rst_n = 1;
        end

        begin
            #1100 reset_vif.rst_n = 0;
            #20  reset_vif.rst_n = 1;
        end

    join_none

    env.run();

end



//--------------------------------
// ZERO WAIT WRITE TEST
//--------------------------------
if ($test$plusargs("apb_write_zerowait_test")) begin

    $display("Running APB WRITE ZERO WAIT TEST");

    apb_wr_zw = new(env.gdmbx);

    env.build();
    env.gen = apb_wr_zw;

    env.run();

end



//--------------------------------
// ZERO WAIT READ TEST
//--------------------------------
if ($test$plusargs("apb_read_zerowait_test")) begin

    $display("Running APB READ ZERO WAIT TEST");

    apb_rd_zw = new(env.gdmbx);

    env.build();
    env.gen = apb_rd_zw;

    env.run();

end



//--------------------------------
// ZERO WAIT WRITE READ TEST
//--------------------------------
if ($test$plusargs("apb_write_read_zerowait_test")) begin

    $display("Running APB WRITE READ ZERO WAIT TEST");

    apb_wr_rd_zw = new(env.gdmbx);

    env.build();
    env.gen = apb_wr_rd_zw;

    env.run();

end



//--------------------------------
// ZERO WAIT RESET TEST
//--------------------------------
if ($test$plusargs("apb_reset_zerowait_test")) begin

    $display("Running APB RESET ZERO WAIT TEST");

    apb_rst_zw = new(env.gdmbx);

    env.build();
    env.gen = apb_rst_zw;

    fork

        begin
            #500 reset_vif.rst_n = 0;
            #20  reset_vif.rst_n = 1;
        end

        begin
            #800 reset_vif.rst_n = 0;
            #20  reset_vif.rst_n = 1;
        end

    join_none

    env.run();

end


endtask

endclass
