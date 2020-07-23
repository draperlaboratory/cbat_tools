# This example contains a function call to foo.

# This tests that WP can inline the function foo based off the regex. With foo
# inlined, WP should find that when argc (RDI) = 5, the execution of the program
# will hit the assert_fail.

# Should return SAT.

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --inline=foo \
    --trip-asserts \
    -- main
}

compile && run
