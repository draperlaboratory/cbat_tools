#!/bin/sh

# This test contains a single call to malloc. This tests uses the
# nondeterministic chaos spec for malloc.

# Should return SAT

run () {
  bap wp \
    --func=foo \
    --show=bir,paths \
    --compare-post-reg-values=RAX \
    --inline=sub_* \
    -- ./bin/main_1.o ./bin/main_2.o
}

run
