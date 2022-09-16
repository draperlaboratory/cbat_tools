#!/bin/sh

# This test contains a single call to malloc. This tests turns off the chaos
# function spec and treats the malloc function as any other function.

# Should return UNSAT

run () {
  bap wp \
    --func=foo \
    --show=bir,paths \
    --compare-post-reg-values=RAX \
    --inline=sub_* \
    --no-chaos=malloc \
    -- ./bin/main_1.o ./bin/main_2.o
}

run
