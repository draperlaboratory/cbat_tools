# This test contains calls to our helper function that just calls
# __VERIFIER_nondet_long. If string2 is NULL, the program will jump to the label
# that frees the memory region. If the program does not jump to any of the gotos,
# there is an assert that the results of the function calls are non-null.

# This tests the default function spec that chaoses the caller-saved registers
# at a function call. This shows that it is possible for string1 to be NULL while
# string2 is non-null, reaching the assert_fail.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --trip-asserts \
    -- main
}

compile && run
