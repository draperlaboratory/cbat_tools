# The modified version of this test adds a check to argc and returns a
# different value if argc = 2.

# This test runs the comparison with a precondition that argc (RDI) cannot be 2.
# As a result, the output of the function should be the same between both
# binaries.

# Should return UNSAT

run () {
  bap wp \
    --func=main \
    --precond="(assert (= RAX (bvmul (bvmul init_RAX RAX) #x0000000000000005)))" \
    --user-func-spec="g,(assert (= RDI #x0000000000000005)),(assert (= RAX (bvmul init_RDI RDI)))" \
    -- main
}

run
