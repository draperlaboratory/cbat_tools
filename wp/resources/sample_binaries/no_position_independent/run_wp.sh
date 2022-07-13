#!/bin/sh

# This tests inlining a function that has been compiled without the  fPIC flag.
# init() returns different values, and if inlined properly, WP should be able
# to capture this.

# Should return SAT.

run () {
  bap wp \
    --func=example \
    --inline=init \
    --compare-post-reg-values=RAX \
    -- ./bin/main_1.so ./bin/main_2.so
}

run
