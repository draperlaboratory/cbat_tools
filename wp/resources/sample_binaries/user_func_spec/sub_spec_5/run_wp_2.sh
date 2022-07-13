#!/bin/sh

# Should return UNSAT: we can trip neither assert because both f and g have postcondition RAX=61

run () {
  bap wp \
    --func=main \
    --user-func-specs="f,(assert true),(assert (= RAX #x0000000000000061));g,(assert true),(assert (= RAX #x0000000000000061))" \
    --trip-assert \
    -- ./bin/main
}

run
