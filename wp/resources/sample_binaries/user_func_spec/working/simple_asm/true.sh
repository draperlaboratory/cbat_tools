# With main.asm, this spec says that
# 1) After greg_memcpy, init_RSI == 3 and RDI == init_RSI
# 2) RAX == 3
# This is because RAX is assigned RDI after greg_memcpy is run

# STATUS: Working! <<-- REMOVE THIS LINE BEFORE MERGING

run () {
  bap wp \
      --func=main \
      --postcond="(assert (= RAX #x0000000000000003))" \
    --user-func-spec="greg_memcpy, (assert true), (assert (and
(= init_RSI #x0000000000000003) (= RDI init_RSI)))" \
    -- ./main
}

run
