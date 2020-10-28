# This tests that the wp-pointer-reg-list flag works as expected.
# Specifically, when num_1 is treated as a pointer, it cannot point to local,
# as local is uninitialized at the start of the function.
 
# Should return UNSAT

set -x

run_unsat () {
  bap wp \
    --func=deref \
    --num-unroll=0 \
    --no-byteweight \
    --mem-offset \
    --syntax-equality \
    -- main_1 main_2
}

run_unsat
