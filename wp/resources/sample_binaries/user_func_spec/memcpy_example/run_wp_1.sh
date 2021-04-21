# Should return SAT: Since when RAX is 0x67, RDI will then trigger the assert(0)
#(= (select mem (bvadd xvar16 RDI)) (select mem (bvadd xvar16 RSI)))

run () {
  bap wp \
      --func=main \
      --precond="(assert (= #x0000000000000000 (bvand #xFFFFFFFF00000000 RAX)))" \
    --postcond="(assert (= #x0000000000000061 (bvand RAX #xFFFFFFFF000000FF)))" \
    --user-func-spec="greg_memcpy, (assert true), (assert (and 
(= (select mem RSI) (select mem RDI))  
(= (select mem (bvadd #x0000000000000001 RSI)) (select mem (bvadd #x0000000000000001 RDI)))
(= (select mem (bvadd #x0000000000000002 RSI)) (select mem (bvadd #x0000000000000002 RDI)))
(= (select mem (bvadd #x0000000000000003 RSI)) (select mem (bvadd #x0000000000000003 RDI)))
(= (select mem (bvadd #x0000000000000004 RSI)) (select mem (bvadd #x0000000000000004 RDI)))
(= (select mem (bvadd #x0000000000000005 RSI)) (select mem (bvadd #x0000000000000005 RDI)))
(= (select mem (bvadd #x0000000000000006 RSI)) (select mem (bvadd #x0000000000000006 RDI)))
(= (select mem (bvadd #x0000000000000007 RSI)) (select mem (bvadd #x0000000000000007 RDI)))
(= (select mem (bvadd #x0000000000000008 RSI)) (select mem (bvadd #x0000000000000008 RDI)))
))" \
    -- ./bin/main
}


run
