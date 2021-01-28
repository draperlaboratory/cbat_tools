# A very simple example that tests a function call to __assert_fail.

# Should return SAT.

run () {
  bap wp \
    --func=main \
    --show=paths,bir \
    --trip-asserts \
    -- ./bin/main
}

run
