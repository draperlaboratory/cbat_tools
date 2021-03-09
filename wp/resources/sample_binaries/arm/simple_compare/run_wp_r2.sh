# This tests that a comparison of the same ARM binary.

# Should return UNSAT.

run () {
  bap wp \
    --func=main \
    --postcond="(assert (= R2_orig R2_mod))" \
    -- ./bin/main.o ./bin/main.o
}

run
