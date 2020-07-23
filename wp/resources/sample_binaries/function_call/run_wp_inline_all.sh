# This example contains a function call to foo.

# This tests that WP can inline all functions. With foo inlined, WP should find
# that when argc (RDI) = 5, the execution of the program will hit the assert_fail.

# Should return SAT.

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
