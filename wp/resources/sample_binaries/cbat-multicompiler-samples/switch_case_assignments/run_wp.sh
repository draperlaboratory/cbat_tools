# This test compares our switch_case_assignment example that has been
# compiled with multiple compilers

# Should return UNSAT

set -x

dummy_dir=../../dummy

compile () {
  make
}

run () {
  bap $dummy_dir/hello_world.out --pass=wp \
    --wp-compare \
    --wp-compare-post-reg-values=RAX \
    --wp-function=process_status \
    --wp-file1=switch_case_assignments-23908.bpj \
    --wp-file2=switch_case_assignments-26471.bpj
}

compile && run
