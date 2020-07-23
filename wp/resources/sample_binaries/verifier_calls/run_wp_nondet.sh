# This tests the function spec for __VERIFIER_nondet, which chaoses the output
# variable. In the case that __VERIFIER_nondet_int() returns a value greater
# than 0, we hit the __VERIFIER_error.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --trip-asserts \
    -- verifier_nondet
}

compile && run
