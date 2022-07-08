#!/bin/sh

# This tests that a comparison of the same ARM binary.

# Should return UNSAT.

run () {
  bap wp \
    --func=main \
    --postcond="(assert (= R1_orig R1_mod))" \
    -- ./bin/main.o ./bin/main.o
}

run
