# This test compares csmith.c compiled with different compilers

# Should return UNSAT

set -x

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --use-fun-input-regs \
    -- csmith-10684 csmith-16812
}

run
