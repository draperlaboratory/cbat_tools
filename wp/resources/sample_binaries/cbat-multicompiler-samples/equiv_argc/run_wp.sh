# This test compares equiv_argc that has been compiled with different compilers.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    -- equiv_argc-6404.bpj equiv_argc-6487.bpj
}

compile && run
