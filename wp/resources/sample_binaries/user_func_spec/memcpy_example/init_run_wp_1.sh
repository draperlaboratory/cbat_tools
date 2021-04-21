# Should return SAT: Since when RAX is 0x67, RDI will then trigger the assert(0)
#(= (select mem (bvadd xvar16 RDI)) (select mem (bvadd xvar16 RSI)))

# --precond="(assert (= #x0000000000000000 (bvand #xFFFFFFFF00000000 RAX)))" \

run () {
  bap wp \
      --func=main \
    --postcond="(assert (= RAX #x0000000000000061)" \
    --user-func-spec="greg_memcpy, (assert true), (assert (and 
(= (select init_mem init_RSI) (select mem RDI))  
(= (select init_mem (bvadd #x0000000000000001 init_RSI)) (select init_mem (bvadd #x0000000000000001 init_RDI)))
(= (select init_mem (bvadd #x0000000000000002 init_RSI)) (select init_mem (bvadd #x0000000000000002 init_RDI)))
(= (select init_mem (bvadd #x0000000000000003 init_RSI)) (select init_mem (bvadd #x0000000000000003 init_RDI)))
(= (select init_mem (bvadd #x0000000000000004 init_RSI)) (select init_mem (bvadd #x0000000000000004 init_RDI)))
(= (select init_mem (bvadd #x0000000000000005 init_RSI)) (select init_mem (bvadd #x0000000000000005 init_RDI)))
(= (select init_mem (bvadd #x0000000000000006 init_RSI)) (select init_mem (bvadd #x0000000000000006 init_RDI)))
(= (select init_mem (bvadd #x0000000000000007 init_RSI)) (select init_mem (bvadd #x0000000000000007 init_RDI)))
(= (select init_mem (bvadd #x0000000000000008 init_RSI)) (select init_mem (bvadd #x0000000000000008 init_RDI)))
(= (select init_mem (bvadd #x0000000000000009 init_RSI)) (select init_mem (bvadd #x0000000000000009 init_RDI)))
(= (select init_mem (bvadd #x000000000000000A init_RSI)) (select init_mem (bvadd #x000000000000000A init_RDI)))
(= (select init_mem (bvadd #x000000000000000B init_RSI)) (select init_mem (bvadd #x000000000000000B init_RDI)))
(= (select init_mem (bvadd #x000000000000000C init_RSI)) (select init_mem (bvadd #x000000000000000C init_RDI)))
(= (select init_mem (bvadd #x000000000000000D init_RSI)) (select init_mem (bvadd #x000000000000000D init_RDI)))
(= (select init_mem (bvadd #x000000000000000E init_RSI)) (select init_mem (bvadd #x000000000000000E init_RDI)))
(= (select init_mem (bvadd #x000000000000000F init_RSI)) (select init_mem (bvadd #x000000000000000F init_RDI)))
))" \
    -- ./bin/main
}


run
