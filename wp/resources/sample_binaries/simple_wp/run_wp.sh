# A simple example that assert_fails when argc = 3.

# WP finds the input value to main which will result in
# reaching assert_fail during execution.

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
