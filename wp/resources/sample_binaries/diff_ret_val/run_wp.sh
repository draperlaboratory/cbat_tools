#!/bin/sh

# A simple test that shows an instance where WP catches a function that has
# different return values between the two binaries. In this case, main_1 returns
# a 2 and main_2 returns a 5.

# Should return SAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    -- ./bin/main_1 ./bin/main_2
}

run
