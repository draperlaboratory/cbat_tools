#!/bin/sh

# This tests that an indirect call with no return does not have
# its stack pointer incremented as part of our indirect call spec.

run () {
  bap wp \
    --func=indirect_call \
    --compare-func-calls \
    --postcond="(assert (and (= RSP_orig (bvadd init_RSP_orig #x0000000000000008)) (= RSP_mod (bvadd init_RSP_mod #x0000000000000008))))" \
    -- ./bin/main_1 ./bin/main_2
}

run
