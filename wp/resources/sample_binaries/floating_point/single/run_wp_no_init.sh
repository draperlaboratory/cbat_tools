#!/bin/sh

# This test does not call the init-mem flag. WP would not know the value stored
# into YMM0.

# Should return SAT.

run () {
  bap wp \
    --func=foo \
    --show=bir \
    --postcond="(assert (= ((_ extract 127 0) YMM0) #x0000000000000000000000003fa00000))" \
    -- ./bin/main
}

run
