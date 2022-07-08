#!/bin/sh

# A test that compares two binaries that perform an addition operation on two
# floating point numbers. The values added differ between the two binaries.

# Should return SAT

run () {
  bap wp \
    --func=foo \
    --init-mem \
    --compare-post-reg-values=YMM0 \
    -- ./bin/main_1 ./bin/main_2
}

run
