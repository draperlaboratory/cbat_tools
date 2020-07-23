# A simple example that assert_fails when argc = 3.

# Tests a user defined precondition that argc/RDI = 2. In this case, it is
# impossible to hit assert_fail during execution.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --precond="(assert (= RDI #x0000000000000000))" \
    -- main
}

compile && run
