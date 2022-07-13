#!/bin/sh

# This example returns UNSAT when the following --user-func-specs flag is included.
# This example returns SAT when no --user-func-specs flag is inluded.
# This example demonstrates a comparative case of using --user-func-specs

run () {
  bap wp \
    --func=main \
    --show=paths \
    --compare-post-reg-values=RAX \
    --user-func-specs="g,(assert true),(assert (= RAX #x0000000000000067))" \
    -- ./bin/main_1 ./bin/main_2
}

run
