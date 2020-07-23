# This test contains multiple calls to calloc in nested if statements.
# After all the calls to calloc, there is an assert that none of the results
# were NULL. This tests that the nested ifs ensure the values of all the
# strings are non-null at the time of the assert.

# This test uses the function spec for calloc which chaoses the output of each
# function call. Allowing us to search the space when calloc returns both a null
# or non-null result.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=nestedIfExample \
    --trip-asserts \
    -- main
}

compile && run
