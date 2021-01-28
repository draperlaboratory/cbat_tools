# This tests the function spec to __VERIFIER_assume. If the assumption that
# x > 0 holds, it is impossible to hit the case where there is a __VERIFIER_error.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --trip-asserts \
    -- ./bin/verifier_assume_unsat
}

run
