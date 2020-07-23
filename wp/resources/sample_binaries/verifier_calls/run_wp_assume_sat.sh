# This tests the function spec for __VERIFIER_error, which should result in a
# precondition of false.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --trip-asserts \
    -- verifier_assume_sat
}

compile && run
