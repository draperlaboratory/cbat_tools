# This test contains a function with two nested calls to foo then bar.

# Without inlining, we only summarize the first call (foo), and do not inspect
# the second call (bar). As a result, we do not find the assert_fail.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --trip-asserts \
    --fun-specs=chaos-caller-saved \
    -- ./bin/main
}

run
