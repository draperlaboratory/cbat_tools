# With main.asm, this spec says that
# 1) Inside function greg_memcpy, RDI becomes init_RSI
# 2) RAX ends up with value 2
# This is because RSI is assigned to 2, then we run greg_memcpy, then RAX is assigned RDI
# This returns UNSAT

# STATUS: Working! <<-- REMOVE THIS LINE BEFORE MERGING

run () {
  bap wp \
      --func=main \
      --show="precond-internal"\
      --postcond="(assert (= RAX #x0000000000000002))" \
      --user-func-spec="greg_memcpy, (assert true), (assert (= init_RSI RDI))" \
    -- ./main
}


run
