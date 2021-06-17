This folder contains four tests that test the basic logic of subroutine specs.
In each case, we build the weakest precondition for the subroutine that should
look like the following:

`run_wp_1.sh` - true & (false => false), should return UNSAT

`run_wp_2.sh` - true & (true => false), should return SAT

`run_wp_3.sh` - true & (RAX=4 => RAX=4), should return UNSAT

`run_wp_4.sh` - RAX=4 & (RAX=4 => RAX=4), should return SAT
