# This test contains multiple calls to calloc. At each call, if the result was
# NULL, the program jumps to the label that frees the memory region.
# If the program does not jump to any of the gotos, there is an assert that
# all the result to calloc are non-null.

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
    --func=gotoExample \
    --trip-asserts \
    -- main
}

compile && run
