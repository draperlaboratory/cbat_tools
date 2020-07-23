# Stubs the lines of assembly that retrowrite adds to the beginning of each
# label. At the end of the subroutine, the registers between both binaries
# should be equal.

# This inlines the call to __afl_maybe_log which should pop
# the stack pointer at the end of the call.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --inline=__afl_maybe_log \
    -- main_1.bpj main_2.bpj
}

compile && run
