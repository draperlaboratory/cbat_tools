# With main.asm, this spec says that
# 0) [RSI] and [RSP] aren't "close" to each other
# 1) the bottom 8 bits of [RSI] is equal to 0x03
# 2) the bottom 8 bits of [RSI] and [RDI] are equal
# And uses these to prove...
# 3) the bottom 8 bits of RAX is equal to 0x03
# This is because RAX is assinged to [RDI] 

# STATUS: Working! <<-- REMOVE THIS LINE BEFORE MERGING

run () {
  bap wp \
      --func=main \
      --precond="(assert (= RSP (bvadd RSI #x00000000000000FF)))"\
      --postcond="(assert (= ((_ extract 7 0) RAX) #x03))" \
      --user-func-spec="subroutine, (assert true), (assert (and 
(= (select init_mem init_RSI) (select mem RDI))
))" \
    -- ./main
}


run
