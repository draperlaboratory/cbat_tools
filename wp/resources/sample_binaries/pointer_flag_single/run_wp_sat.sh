# This tests the single binary case of the --wp-poitner-reg-list flag. In this
# case, we ensure that the program cannot take input that points to an
# uninitialized region on the stack. Without the flag, this is possible.

# Should return SAT

set -x

run () {
  bap wp \
    --func=foo \
    --postcond="(assert (not (= RAX #x00000000deadbeef)))" \
    -- ./bin/main
}

run
