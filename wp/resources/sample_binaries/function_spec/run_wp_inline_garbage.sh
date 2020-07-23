# This test contains a call to foo which returns 3. In main, in the case that
# foo returns 5, we assert_fail. This should be impossible.

# This tests passes in a regex that doesn't match any function.
# As a result, no function is inlined, and the output to foo will be chaosed.

# Should return SAT.

set -x

compile () {
  make
}

run () {
    bap wp \
      --func=main \
      --inline=NONEXISTENTGARBAGE \
      --trip-asserts \
      -- main
}

compile && run
