# With main.asm, this spec says that
# 0) [RSI] and [RSP] aren't "close" to each other
# 1) [RSI] is equal to 0x0000000000000003 (see "mov QWORD [rsi], 3" in main.asm)
# 2) [RSI] and [RDI] are equal
# And uses these to prove...
# 3) RAX is equal to 0x03
# This is because RAX is assinged to [RDI] in main.asm
# This spec is the same as full_reg_memcpy_asm/true.sh except that we use a forall
#   statement over the register indexes in RDI and RSI

# STATUS: not working <<-- REMOVE THIS LINE BEFORE MERGING

#precond: --precond="(assert (bvuge RSP #x0000000000000000))" \
# postcond: 

run () {
  bap wp \
      --func=main \
      --show="refuted-goals" \
      --postcond="(assert (= RAX #x0000000000000003))" \
      --user-func-spec="subroutine, (assert true), 
(assert (forall ((new_var (_ BitVec 64))) 
(=> 
 (and (bvule #x0000000000000000 new_var)
 (bvule new_var #x0000000000000007))
(= (select init_mem (bvadd init_RSI new_var)) (select mem (bvadd RDI new_var))
))))" \
    -- ./main
}


run
