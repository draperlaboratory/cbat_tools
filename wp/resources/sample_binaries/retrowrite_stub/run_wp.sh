# Stubs the lines of assembly that retrowrite adds to the beginning of each
# label. At the end of the subroutine, the registers between both binaries
# should be equal.

# This tests that the function spec for __afl_maybe_log
# properly pops the stack pointer at the end of the function.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --no-glibc-runtime \
    -- main_1 main_2
}

run
