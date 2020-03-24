# A simple example that assert_fails when argc = 3.

# Tests a user defined precondition that argc/RDI = 2. In this case, it is
# impossible to hit assert_fail during execution.

# Should return UNSAT

set -x

compile () {
  make
}

run () {
  bap main --pass=wp --wp-precond="(assert (= RDI #x0000000000000002))"
}

compile && run
