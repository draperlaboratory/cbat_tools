# This tests the function spec for __VERIFIER_error, which should result in a
# precondition of false.

# Should return SAT

run () {
  bap wp \
    --func=main \
    --trip-asserts \
    -- ./bin/verifier_assume_sat
}

run
