# This tests that the absence wp-pointer-reg-list flag works as expected.
# Specifically, differing return value should be found between programs because
# in main_1, num_1 cannot be greater than 12. In main_2, num1 can point to local
# and become 42, which is greater than 12. This results in main_1 returning 
# 0 and main_2 returning -1.

# Should return SAT

set -x

run_sat () {
  bap wp \
    --func=deref \
    --num-unroll=0 \
    --no-byteweight \
    --mem-offset \
    --show=bir,refuted-goals,paths \
    --compare-post-reg-values=R12,R13,R14,R15,RBX,RSP,RBP,RAX \
    --precond="(assert (= mem_orig mem_mod))" \
    -- main_1 main_2
}

run_sat
