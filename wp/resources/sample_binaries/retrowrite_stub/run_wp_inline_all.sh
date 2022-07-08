#!/bin/sh

# Stubs the lines of assembly that retrowrite adds to the beginning of each
# label. At the end of the subroutine, the registers between both binaries
# should be equal.

# This inlines all function calls which should pop
# the stack pointer at the end of each call.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --inline=.* \
    --no-glibc-runtime \
    -- ./bin/main_1 ./bin/main_2
}

run
