# This test compares csmith.c compiled with different compilers.

# This test inlines all function calls rather than using function summaries.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --use-fun-input-regs \
    --inline=.* \
    -- csmith-10684 csmith-16812
}

run
