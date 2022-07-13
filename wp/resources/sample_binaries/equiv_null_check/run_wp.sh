#!/bin/sh

# The modified binary adds a null check after the call to malloc. In the case
# that malloc returns NULL, the modified binary will hit an assert_fail.

# Should return SAT.

run () {
  bap wp \
    --func=main \
    --trip-asserts \
    --compare-post-reg-values=RAX \
    -- ./bin/main_1 ./bin/main_2
}

run
