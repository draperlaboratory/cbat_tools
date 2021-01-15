# Should return SAY, since (false /\ (RAX = 4 => RAX = 4)) is always false

run () {
  bap wp \
    --func=main \
    --postcond="(assert (= RAX #x0000000000000004))" \
    --user-func-spec="g,(assert false),(assert (= RAX #x0000000000000004))" \
    -- main
}

run
