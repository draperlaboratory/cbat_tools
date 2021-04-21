# Should return SAT: Since when RAX is 0x67, RDI will then trigger the assert(0)
#(= (select mem (bvadd xvar16 RDI)) (select mem (bvadd xvar16 RSI)))

# Some lines taken out:
# --precond="(assert (= #x0000000000000000 (bvand #xFFFFFFFF00000000 RAX)))" \
# 
#

run () {
  bap wp \
      --func=main \
      --show="precond-internal,colorful"\
      --postcond="(assert (= RAX #x0000000000000061))" \
    --user-func-spec="greg_memcpy, (assert true), (assert (or
(= (select mem (bvadd #x0000000000000000 RDI)) #x61)
(= (select mem (bvadd #x0000000000000001 RDI)) #x61)
(= (select mem (bvadd #x0000000000000002 RDI)) #x61)
(= (select mem (bvadd #x0000000000000003 RDI)) #x61)
(= (select mem (bvadd #x0000000000000004 RSP)) #x61)
(= (select mem (bvadd #x0000000000000005 RSP)) #x61)
(= (select mem (bvadd #x0000000000000006 RSP)) #x61)
(= (select mem (bvadd #x0000000000000007 RSP)) #x61)
(= (select mem (bvadd #x0000000000000008 RSP)) #x61)
(= (select mem (bvadd #x0000000000000009 RSP)) #x61)
(= (select mem (bvadd #x000000000000000A RSP)) #x61)
(= (select mem (bvadd #x000000000000000B RSP)) #x61)
(= (select mem (bvadd #x000000000000000C RSP)) #x61)
(= (select mem (bvadd #x000000000000000D RSP)) #x61)
(= (select mem (bvadd #x000000000000000E RSP)) #x61)
(= (select mem (bvadd #x000000000000000F RSP)) #x61)))" \
    -- ./bin/main
}


run
