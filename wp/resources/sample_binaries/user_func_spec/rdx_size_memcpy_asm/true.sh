# With main.asm, this spec says that
# 0) [RSI] and [RSP] aren't "close" to each other
# 1) [RSI] is equal to 0x0000000000000003 (see "mov QWORD [rsi], 3" in main.asm)
# 2) [RSI] and [RDI] are equal
# And uses these to prove...
# 3) RAX is equal to 0x03
# This is because RAX is assinged to [RDI] in main.asm

# STATUS: Working <<-- REMOVE THIS LINE BEFORE MERGING
 
run () {
  bap wp \
      --func=main \
      --precond="(assert (and 
(bvule #x0000000000000000 RDX)
(bvule RDX #x00000000000000FF)
(= RSP (bvadd RSI #x00000000000000FF))
))"\
      --postcond="(assert (forall ((new_var (_ BitVec 64))) (and
(bvule #x0000000000000000 RDX)
(bvule RDX #x00000000000000FF)
(bvule #x0000000000000000 new_var)
(bvule new_var init_RDX)
(= (select mem (bvadd RDI new_var)) (select mem (bvadd RSI new_var)))
)))" \
      --user-func-spec="subroutine, (assert true), (assert (forall ((new_var (_ BitVec 64))) (and 
(bvule #x0000000000000000 new_var)
(bvule new_var init_RDX)
(= (select init_mem (bvadd init_RSI new_var)) (select mem (bvadd RDI new_var))
))))" \
    -- ./main
}


run
