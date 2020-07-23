# This test contains a function with two nested calls to foo then bar.

# Here, we are inlining all function calls, allowing us to inspect both foo and
# bar. This allows WP to find the case where assert_fail is reach in bar.

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
