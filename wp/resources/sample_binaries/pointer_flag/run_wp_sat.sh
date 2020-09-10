# This is a test that tests that the wp-pointer-reg-list flag works as expected.
# Specifically, the function foo tries to use differing
# return addresses that are pushed onto the stack to cause a different return
# value between functions. The abscence of the flag should allow the pointer
# argument in RDI to be used to point to this return address, as it lives
# on the uninitialized portion of the stack at the start of the function.

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
    -- main_1 main_2
}

run_sat
