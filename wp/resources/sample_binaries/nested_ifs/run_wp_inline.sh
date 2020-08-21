# This test analyzes both the gotoExample and nestedIfExample.

# This test inlines all the calls to calloc rather than running the calloc
# function spec.

# Should return UNSAT

set -x

run () {
  bap wp \
    --func=main \
    --inline=.* \
    --trip-asserts \
    -- main
}

run
