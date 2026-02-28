RTL=../rtl/apb_slave_design.sv
INF=../env/apb_interface.sv
PKG=../test/apb_pkg.sv
TOP=../top/apb_top.sv
INC=+incdir+../test/ +incdir+../env/ +incdir+../top/

COM=vcs -full64 -sverilog -kdb -debug_access+all ${RTL} ${INF} ${PKG} ${TOP} ${INC}
compile:
			${COM}
RUN=vcs -R -full64 -sverilog  -kdb -debug_access+all +ntb_random_seed_automatic -override_timescale=1ps/1ps ${RTL} ${INF} ${PKG} ${TOP} ${INC}


run: 
	${RUN}

tc1:
	$(RUN) -cm_dir $(TEST1)_coverage.vdb +$(TEST1) -l $(TEST1).log; urg -dir $(TEST1)_coverage.vdb -report $(TEST1)_report

TEST1=apb_write_read_test

tc2:
	$(RUN) -cm_dir $(TEST2)_coverage.vdb +$(TEST2) -l $(TEST2).log; urg -dir $(TEST2)_coverage.vdb -report $(TEST2)_report

TEST2=apb_write_test

tc3:
	$(RUN) -cm_dir $(TEST3)_coverage.vdb +$(TEST3) -l $(TEST3).log; urg -dir $(TEST3)_coverage.vdb -report $(TEST3)_report

TEST3=apb_read_test

tc4:
	$(RUN) -cm_dir $(TEST4)_coverage.vdb +$(TEST4) -l $(TEST4).log; urg -dir $(TEST4)_coverage.vdb -report $(TEST4)_report

TEST4=apb_slverr_test


tc5:
	$(RUN) -cm_dir $(TEST5)_coverage.vdb +$(TEST5) -l $(TEST5).log; urg -dir $(TEST5)_coverage.vdb -report $(TEST5)_report

TEST5=apb_reset_test

# ZERO WAIT STATE

tc6:
	$(RUN) -cm_dir $(TEST6)_coverage.vdb +$(TEST6) +zerowaitstate -l $(TEST6).log; urg -dir $(TEST6)_coverage.vdb -report $(TEST6)_report

TEST6=apb_write_read_zerowait_test

tc7:
	$(RUN) -cm_dir $(TEST7)_coverage.vdb +$(TEST7) +zerowaitstate -l $(TEST7).log; urg -dir $(TEST7)_coverage.vdb -report $(TEST7)_report

TEST7=apb_write_zerowait_test

tc8:
	$(RUN) -cm_dir $(TEST8)_coverage.vdb +$(TEST8) +zerowaitstate -l $(TEST8).log; urg -dir $(TEST8)_coverage.vdb -report $(TEST8)_report

TEST8=apb_read_zerowait_test

tc9:
	$(RUN) -cm_dir $(TEST9)_coverage.vdb +$(TEST9) +zerowaitstate -l $(TEST9).log; urg -dir $(TEST9)_coverage.vdb -report $(TEST9)_report

TEST9=apb_slverr_zerowait_test


tc10:
	$(RUN) -cm_dir $(TEST10)_coverage.vdb +$(TEST10) +zerowaitstate -l $(TEST10).log; urg -dir $(TEST10)_coverage.vdb -report $(TEST10)_report

TEST10=apb_reset_zerowait_test



tc: tc1 tc2 tc3 tc4 tc5 tc6 tc7 tc8 tc9 tc10

merge:
	urg -dir $(TEST1)_coverage.vdb $(TEST2)_coverage.vdb $(TEST3)_coverage.vdb $(TEST4)_coverage.vdb $(TEST5)_coverage.vdb $(TEST6)_coverage.vdb $(TEST7)_coverage.vdb $(TEST8)_coverage.vdb $(TEST9)_coverage.vdb $(TEST10)_coverage.vdb -format both -report merged_report

report:
	firefox merged_report/dashboard.html&

regression: tc merge report

final: merge report

clean:
	rm -rf csrc simv.daidir ucli.key simv *.vpd *.vcd *.log *.dump *.vdb *_test nova* v* *_report



