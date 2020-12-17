# The modified version of this test adds a check to argc and returns a
# different value if argc = 2.

# This test runs the comparison with a precondition that argc RAX is not equal to 7.
# As a result, the output of the function should be the same between both
# binaries.

# Should return SAT

# run
run () {
  bap wp \
    --func=main \
    --show=paths \
    --user-func-spec="g,(assert true),(assert (= RAX #x0000000000000067))" \
    --trip-assert \
    -- main
}

run
