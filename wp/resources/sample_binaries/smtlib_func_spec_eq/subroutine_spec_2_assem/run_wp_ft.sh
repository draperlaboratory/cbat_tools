# The modified version of this test adds a check to argc and returns a
# different value if argc = 2.

# This test runs the comparison with a precondition that argc RAX is not equal to 7.
# As a result, the output of the function should be the same between both
# binaries.

# Should return UNSAT

# More ideal test case
# run () {
#   bap wp \
#     --func=main \
#     --compare-post-reg-values=RAX \
#     --precond="(assert (and (= #x0000000000000000 (bvand RAX_mod #xFFFFFFFF00000000)) (not (= RAX_mod #x0000000000000007))))" \
#     --user-func-spec="foo,(assert (and (= #x0000000000000000 (bvand RDI_orig #xFFFFFFFF00000000)) (not (= RDI_orig #x0000000000000007)))),(assert (and (= #x0000000000000000 (bvand RAX_mod #xFFFFFFFF00000000)) (not (= RAX_mod #x0000000000000007))))" \
#     -- main_1 main_2
# }
#
#
#    --user-func-spec="g,(assert true),(assert (and (= #x0000000000000000 (bvand RAX #xFFFFFFFF00000000)) (= RAX #x0000000000000067)))" \

# run
run () {
  bap wp \
    --func=main \
    --show=paths \
    --user-func-spec="g,(assert false),(assert true)" \
    --trip-assert \
    -- main
}

run
