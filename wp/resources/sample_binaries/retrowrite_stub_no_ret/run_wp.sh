# Stubs the lines of assembly that retrowrite adds to the beginning of each
# label. At the end of the subroutine, the registers between both binaries
# should be equal.

# This tests the __afl_maybe_log spec that it is the callee's
# responsibility to pop the stack pointer.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --no-glibc-runtime \
    -- main_1 main_2
}

run
