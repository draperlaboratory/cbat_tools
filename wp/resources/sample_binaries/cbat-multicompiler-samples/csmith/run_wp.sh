# This test compares csmith.c compiled with different compilers

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --use-fun-input-regs \
    -- csmith-10684.bpj csmith-16812.bpj
}

compile && run
