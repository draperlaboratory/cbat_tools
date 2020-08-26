# This is a test that tests that the wp-pointer-reg-list flag works as expected
# specifically, it calls a function, then tries to use the differing return address that 
# is thereby pushed onto the stack to cause a different return value between functions.
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
