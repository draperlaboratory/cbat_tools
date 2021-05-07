# This tests a loop without an invariant to check. Without the invariant, WP
# wouldn't be able to determine that x is incremented z times.

# Should return SAT.

run () {
  bap wp \
    --num-unroll=0 \
    --func=loop \
    --precond="(assert (bvult RDX #x000000007fffffff))" \
    --postcond="(assert (= RAX init_RDX))" \
    -- ./bin/main
}

run
