# nested loop test two levels deep
# both loops are preserved based on cfg.  Expected value of RAX (j) should be 3
# RAX (j) ends as 2 and not 3.
# Note that by looking at the CFG and compiling with O0, both loops do exist.

# Should return UNSAT

run() {
  bap wp \
    --func=foo \
    --num-unroll=18 \
    --postcond="(assert (not (= RAX #x0000000000000002)))" \
    --no-byteweight \
    -- main_1
}

run_should_be_sat_but_is_not() {
  bap wp \
    --func=foo \
    --num-unroll=18 \
    --postcond="(assert (not (= RAX #x0000000000000003)))" \
    --no-byteweight \
    -- main_1
}

run
