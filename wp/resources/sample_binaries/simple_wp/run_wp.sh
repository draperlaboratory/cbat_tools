# A simple example that assert_fails when argc = 3.

# WP finds the input value to main which will result in
# reaching assert_fail during execution.

# Should return SAT

run () {
  bap wp \
    --func=main \
    --trip-asserts \
    -- ./bin/main
}

run
