# With main.asm, this spec says that
# 1) mem at (RSI + 0) equals 3
# 2) mem at (RSI + 0) equals RDI
# 3) RAX = 3
# This is because the first 8 bits of [RSI] are set to 0x03,
# then subroutine is called, and then RAX is set to RDI

# STATUS: Working! <<-- REMOVE THIS LINE BEFORE MERGING

run () {
  bap wp \
      --func=main \
      --show="precond-internal,colorful"\
      --postcond="(assert (= ((_ extract 7 0) RAX) #x03))" \
      --user-func-spec="subroutine, (assert true), (assert (and (= (select mem init_RSI) #x03) (= (select mem init_RSI) ((_ extract 7 0) RDI) ) ))" \
    -- ./main
}


run
