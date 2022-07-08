#!/bin/sh

# This example returns SAT when no --user-func-specs flag is included.
# This example returns UNSAT when a --user-func-specs flag that specifies RAX is
#   not equal to #x0000000000000067 is added. 

run () {
  bap wp \
    --func=main \
    --show=paths \
    --compare-post-reg-values=RAX,RDI \
    --user-func-specs="g,(assert true),(assert (= RAX #x0000000000000061))" \
    -- ./bin/main_1 ./bin/main_2
}

run
