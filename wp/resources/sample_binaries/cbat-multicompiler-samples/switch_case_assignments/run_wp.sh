# This test compares our switch_case_assignment example that has been
# compiled with multiple compilers

# Should return UNSAT

run () {
  bap wp \
    --compare-post-reg-values=RAX \
    --func=process_status \
    -- ./bin/switch_case_assignments-23908 ./bin/switch_case_assignments-26471
}

run
