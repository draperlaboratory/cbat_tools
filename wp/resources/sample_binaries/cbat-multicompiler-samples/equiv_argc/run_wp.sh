# This test compares equiv_argc that has been compiled with different compilers.

# Should return UNSAT

set -x

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --no-byteweight \
    -- equiv_argc-6404 equiv_argc-6487
}

run
