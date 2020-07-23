# This tests a function that checks if two integers are of the same sign. The
# original binary uses a series of if/then statements to determine this, while
# the second binary determines this with an exclusive or operator. Both should
# be functionally equivalent. The result of same_signs between the two binaries
# should be equal to each other given that the inputs are the same.

# This tests the use of the compare-post-reg-values flag to compare the final
# values of RAX at the end of same_sign's execution.

# Should return UNSAT.

set -x


compile () {
  make
}

run () {
  bap wp \
    --func=same_signs \
    --compare-post-reg-values=RAX \
    -- main_1.bpj main_2.bpj
}

compile && run
