# This tests the single binary case of the --wp-pointer-reg-list flag. In this
# case, we ensure that the program cannot take input that points to an
# uninitialized region on the stack. With the flag, this is not possible.

# Should return UNSAT

set -x

run () {
  bap wp \
    --func=foo \
    --postcond="(assert (not (= RAX #x00000000deadbeef)))" \
    --pointer-reg-list=RDI  \
    -- main

}

run
