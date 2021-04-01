# This tests mapping function names from the original binary to their names in
# the modified binary. In this example, function names are prepended with test_
# in the modified binary.

# If WP is able to properly map function names, it should know that foo and
# test_foo represent the same function.

# Should return UNSAT

run () {
  bap wp \
    --func=foo \
    --func-name-map="\(.*\),test_\1" \
    --compare-post-reg-values=RAX,R12,R13,R14,R15,RBX,RSP,RBP \
    --show=bir,paths \
    -- ./bin/main_1 ./bin/main_2
}

run
