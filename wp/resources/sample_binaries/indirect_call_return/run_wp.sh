# This tests that an indirect call with a return has its stack pointer incremented
# as part of our indirect call spec.

set -x

dummy_dir=../dummy

compile () {
  make
}

run () {
  bap wp \
    --func=indirect_call \
    --compare-func-calls \
    --postcond="(assert (and (= RSP_orig (bvadd init_RSP_orig #x0000000000000008)) (= RSP_mod (bvadd init_RSP_mod #x0000000000000008))))" \
    -- main_1 main_2
}

run
