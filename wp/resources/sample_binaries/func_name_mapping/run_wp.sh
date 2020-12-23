# This tests mapping function names from the original binary to their names in
# the modified binary. In this example, function names are prepended with test_
# in the modified binary.

# If WP is able to properly map function names, it should know that foo and
# test_foo, and bar and test_bar are pairs of the same function.

# Should return UNSAT

run () {
  bap wp \
    --func=foo \
    --func-names-mapping="fun name -> 'test_' ^ name" \
    --compare-post-reg-values=RAX,R12,R13,R14,R15,RBX,RSP,RBP \
    -- main_1 main_2
}

run
