# The modified version of this test adds a check to argc and returns a
# different value if argc = 2.

# This test runs the comparison with a precondition that argc RAX is not equal to 7.
# As a result, the output of the function should be the same between both
# binaries.

# Should return UNSAT, since RDI=9 ensures us that the right value for RDI is picked
# to ensure RAX = init_RDI * RDI

# run
run () {
  bap wp \
    --func=main \
    --show=paths \
    --postcond="(assert (= RAX (bvmul #x0000000000000007 RDI)))" \
    --user-func-spec="g,(assert (= RDI #x0000000000000007)),(assert (= RAX (bvmul init_RDI RDI)))" \
    -- main
}

run
