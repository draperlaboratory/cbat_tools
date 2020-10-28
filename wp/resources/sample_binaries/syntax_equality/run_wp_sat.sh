# This tests that main_1 and main_2 are not syntactically equal to each other

# Should return SAT

set -x

run_unsat () {
  bap wp \
    --func=deref \
    --num-unroll=0 \
    --no-byteweight \
    --mem-offset \
    --syntax-equality \
    --compare-post-reg-values=R12,R13,R14,R15,RBX,RSP,RBP,RAX \
    -- main_1 main_2
}

run_unsat
