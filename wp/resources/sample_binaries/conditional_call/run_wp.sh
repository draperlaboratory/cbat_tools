# This tests a conditional function call to __assert_fail. It is impossible to
# reach __assert_fail in this case.

# Should return UNSAT.

run () {
  bap wp \
    --func=main \
    --show=paths,bir \
    --trip-asserts \
    --fun-specs=chaos-caller-saved \
    -- ./bin/main
}

run
