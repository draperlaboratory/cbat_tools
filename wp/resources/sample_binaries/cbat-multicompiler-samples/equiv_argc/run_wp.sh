# This test compares equiv_argc that has been compiled with different compilers.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --no-byteweight \
    --fun-specs=chaos-caller-saved \
    -- ./bin/equiv_argc-6404 ./bin/equiv_argc-6487
}

run
