# This test compares csmith.c compiled with different compilers

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --use-fun-input-regs \
    -- ./bin/csmith-10684 ./bin/csmith-16812
}

run
