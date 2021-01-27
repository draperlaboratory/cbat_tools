# The modified version of this test adds a check to argc and returns a
# different value if argc = 2.

# This test runs the comparison with a precondition that argc RAX is not equal to 7.
# As a result, the output of the function should be the same between both
# binaries.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --precond="(assert (and (= #x0000000000000000 (bvand RAX_mod #xFFFFFFFF00000000)) (not (= RAX_mod #x0000000000000007))))" \
    --user-func-spec="foo,,(assert (and (= #x0000000000000000 (bvand RAX_mod #xFFFFFFFF00000000)) (not (= RAX_mod #x0000000000000007))))" \
    -- main_1 main_2
}

run
