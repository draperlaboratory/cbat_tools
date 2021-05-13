# This tests a loop without an invariant to check. Without the invariant, WP
# wouldn't be able to determine that x is 5 at the end of the function.

# Should return SAT.

run () {
  bap wp \
    --num-unroll=5 \
    --func=loop \
    --postcond="(assert (= RAX #x0000000000000005))" \
    -- ./bin/main
}

run
