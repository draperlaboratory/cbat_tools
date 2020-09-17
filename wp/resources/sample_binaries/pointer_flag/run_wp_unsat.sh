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
    --show=bir,refuted-goals,paths \
    --compare-post-reg-values=R12,R13,R14,R15,RBX,RSP,RBP,RAX \
    --pointer-reg-list=ABC,RDI \
    --precond="(assert (= mem_orig mem_mod))" \
    -- main_1 main_2
}

run_unsat
