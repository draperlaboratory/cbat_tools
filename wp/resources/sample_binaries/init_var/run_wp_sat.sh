# A simple test that adds 1 to the input.

# Runs WP on the function foo with a postcondition that states that the foo's
# output (RAX) should be equal to the its input (the initial value of RDI) + 2,
# which is impossible due to the definition of foo.

# Should return SAT

set -x

compile () {
  make
}

run () {
  bap wp \
    --func=foo \
    --postcond="(assert (= RAX (bvadd init_RDI #x0000000000000002)))" \
    -- main
}

compile && run
