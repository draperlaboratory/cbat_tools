# This test contains calls to our helper function that just calls
# __VERIFIER_nondet_long. If string2 is NULL, the program will jump to the label
# that frees the memory region. If the program does not jump to any of the gotos,
# there is an assert that the results of the function calls are non-null.

# This tests inlining my_string_alloc in order to analyze the call to
# __VERIFIER_nondet_long, and show that the non-deterministic nature of
# __VERIFIER_nondet_long can cause execution to reach assert_fail.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --inline=.* \
    --trip-asserts \
    -- main
}

compile && run
