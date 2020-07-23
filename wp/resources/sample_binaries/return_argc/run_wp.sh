# This example returns the first argument to main.

# This tests a user defined postcondition. In this case, the postcondition of
# RAX = 0 will not always be fulfilled in the binary.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=main \
    --postcond="(assert (= RAX #x0000000000000000))" \
    -- main
}

compile && run
