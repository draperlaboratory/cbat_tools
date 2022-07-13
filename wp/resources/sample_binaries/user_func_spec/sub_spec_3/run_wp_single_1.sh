#!/bin/sh

# This example returns SAT when no --user-func-specs flag is included.
# This example returns UNSAT when the following --user-func-specs flag is added.

run () {
  bap wp \
    --func=main \
    --show=paths \
    --user-func-specs="g,(assert true),(assert (= RAX #x0000000000000061))" \
    --trip-assert \
    -- ./bin/main_1
}

run
