# This tests WP's ability to unroll a simple loop 5 times. It should be
# able to tell that x is being incremented.

# Should return UNSAT.

run () {
  bap wp \
    --num-unroll=5 \
    --func=loop \
    --postcond="(assert (= RAX #x0000000000000005))" \
    -- ./bin/main
}

run
