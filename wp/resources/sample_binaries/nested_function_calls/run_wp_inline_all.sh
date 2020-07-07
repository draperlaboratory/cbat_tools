# This test contains a function with two nested calls to foo then bar.

# Here, we are inlining all function calls, allowing us to inspect both foo and
# bar. This allows WP to find the case where assert_fail is reach in bar.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap main --pass=wp --wp-inline=.* --wp-trip-asserts
}

compile && run
