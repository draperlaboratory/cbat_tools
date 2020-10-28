# This tests that main_2 is syntactically equal to itself

# Should return UNSAT

set -x

run_unsat () {
  bap wp \
    --func=deref \
    --num-unroll=0 \
    --no-byteweight \
    --mem-offset \
    --syntax-equality \
    -- main_2 main_2
}

run_unsat
