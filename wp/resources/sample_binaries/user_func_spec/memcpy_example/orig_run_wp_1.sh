# Should return SAT: Since when RAX is 0x67, RDI will then trigger the assert(0)
#(= (select mem (bvadd xvar16 RDI)) (select mem (bvadd xvar16 RSI)))

run () {
  bap wp \
    --func=main \
    --precond="(assert (and (= #x0000000000000000 (bvand RAX #xFFFFFFFF00000000))))" \
    --postcond="(assert (and (= #x0000000000000000 (bvand RAX #xFFFFFFFF00000000)) (= RAX #x0000000000000067)))" \
    --user-func-spec="greg_memcpy,(assert true),(declare-const new_var (_ BitVec 64)) (assert (implies (bvult new_var init_RDX) (= (select mem (bvadd new_var init_RDI)) (select mem (bvadd new_var init_RSI)))))" \
    -- ./bin/main
}


run
