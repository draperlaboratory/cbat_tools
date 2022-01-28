# This test checks that the init-mem flag is able to read the floating point
# number into YMM0.

# Should return UNSAT.

run () {
  bap wp \
    --func=foo \
    --init-mem \
    --postcond="(assert (= ((_ extract 127 0) YMM0) #x0000000000000000000000003fa00000))" \
    -- ./bin/main
}

run
