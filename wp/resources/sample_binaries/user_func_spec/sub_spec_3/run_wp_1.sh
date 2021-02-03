# This example returns SAT when no --user-func_spec flag is included.
# This example returns UNSAT when a --user_func_spec flag that specifies RAX is
#   not equal to #x0000000000000067 is added. 

run () {
  bap wp \
    --func=main \
    --show=paths \
    --user-func-spec="g,(assert true),(assert (= RAX #x0000000000000061))" \
    --trip-assert \
    -- ./bin/main
}

run
