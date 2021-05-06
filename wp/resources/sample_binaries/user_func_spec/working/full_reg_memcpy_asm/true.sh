# With main.asm, this spec says that
# 0) [RSI] and [RSP] aren't "close" to each other
# 1) [RSI] is equal to 0x0000000000000003 (see "mov QWORD [rsi], 3" in main.asm)
# 2) [RSI] and [RDI] are equal
# And uses these to prove...
# 3) RAX is equal to 0x03
# This is because RAX is assinged to [RDI] in main.asm

# STATUS: Working! <<-- REMOVE THIS LINE BEFORE MERGING

run () {
  bap wp \
      --func=main \
      --precond="(assert (= RSP (bvadd RSI #x00000000000000FF)))"\
      --postcond="(assert (= RAX #x0000000000000003))" \
      --user-func-spec="subroutine, (assert true), (assert (and 
(= (select init_mem init_RSI) (select mem RDI))
(= (select init_mem (bvadd init_RSI #x0000000000000001)) (select mem (bvadd RDI #x0000000000000001)))
(= (select init_mem (bvadd init_RSI #x0000000000000002)) (select mem (bvadd RDI #x0000000000000002)))
(= (select init_mem (bvadd init_RSI #x0000000000000003)) (select mem (bvadd RDI #x0000000000000003)))
(= (select init_mem (bvadd init_RSI #x0000000000000004)) (select mem (bvadd RDI #x0000000000000004)))
(= (select init_mem (bvadd init_RSI #x0000000000000005)) (select mem (bvadd RDI #x0000000000000005)))
(= (select init_mem (bvadd init_RSI #x0000000000000006)) (select mem (bvadd RDI #x0000000000000006)))
(= (select init_mem (bvadd init_RSI #x0000000000000007)) (select mem (bvadd RDI #x0000000000000007)))
))" \
    -- ./main
}


run
