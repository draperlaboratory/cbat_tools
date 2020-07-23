# This binary tests CBAT's ability to unroll loops. In this test, there is a for
# loop that increments a counter, and if that counter has a specific value at
# the end of the loop, we hit an assert(0).

# If we are able to properly unroll loops, we should be able to reach that
# assert(0) in the analysis.

# Should return SAT

set -x

compile() {
  make
}

run() {
  bap wp \
    --func=main \
    --num-unroll=2 \
    --trip-asserts \
    -- main
}

compile && run
