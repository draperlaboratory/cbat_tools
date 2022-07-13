#!/bin/sh

# Should return SAT, since (false /\ (RAX = 4 => RAX = 4)) is always false

run () {
  bap wp \
    --func=main \
    --postcond="(assert (= RAX #x0000000000000004))" \
    --user-func-specs="g,(assert false),(assert (= RAX #x0000000000000004))" \
    -- ./bin/main
}

run
