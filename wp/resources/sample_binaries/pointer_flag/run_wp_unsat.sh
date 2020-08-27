# This is a test that tests that the wp-pointer-reg-list flag works as expected.
# Specifically, the function foo tries to use differing
# return addresses that are pushed onto the stack to cause a different return
# value between functions. The inclusion of the flag should prevent the pointer
# argument in RDI from being used to point to this return address, as it lives
# on the uninitialized portion of the stack at the start of the function.

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
          --pointer-reg-list=RDI \
          -- main_1 main_2

  
  }

run_unsat
