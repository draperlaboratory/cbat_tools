# Should return SAT, since (RAX = 4 /\ (RAX = 4 => RAX = 4)) is
# not always true, since RAX may be other values other than 4

run () {
  bap wp \
    --func=main \
    --postcond="(assert (= RAX #x0000000000000004))" \
    --user-func-spec="g,(assert (= RAX #x0000000000000004)),(assert (= RAX #x0000000000000004))" \
    -- main
}

run
