package apb_pkg;

   event e1; 
// Core environment files
`include "apb_transaction.sv"
`include "apb_generator.sv"
`include "apb_driver.sv"
`include "apb_monitor.sv"
`include "apb_predictor.sv"
`include "apb_scoreboard.sv"
`include "apb_environment.sv"

// Individual test classes
`include "apb_write_read_test.sv"
`include "apb_write_test.sv"
`include "apb_read_test.sv"
`include "apb_slverr_test.sv"
`include "apb_reset_test.sv"

`include "apb_write_read_zerowait_test.sv"
`include "apb_write_zerowait_test.sv"
`include "apb_read_zerowait_test.sv"
`include "apb_slverr_zerowait_test.sv"
`include "apb_reset_zerowait_test.sv"

// Base test LAST (because it declares handles to all tests)
`include "apb_test.sv"

endpackage
