# Ideally, this code should compare the 64 bits after [[RSI]] is the same as the
#   64 bits after [RDI]
# (= ((_ extract (+ new_var 7) new_var) RAX) ((_ extract 7 0) RDI))

run () {
  bap wp \
      --func=main \
      --show="precond-internal,colorful"\
      --postcond="(declare-const new_var Int) (assert (and 
(= (select mem (bvadd #x0000000000000001 RSI)) ((_ extract 7 0) RAX))
))" \
      --user-func-spec="greg_memcpy, (assert true), (assert (and
(= (select mem init_RSI) #x03)
(= (select mem (bvadd #x0000000000000001 init_RSI)) #x00)
(= (select mem (bvadd #x0000000000000002 init_RSI)) #x00)
(= (select mem (bvadd #x0000000000000003 init_RSI)) #x00)
(= (select mem (bvadd #x0000000000000004 init_RSI)) #x00)
(= (select mem (bvadd #x0000000000000005 init_RSI)) #x00)
(= (select mem (bvadd #x0000000000000006 init_RSI)) #x00)
(= (select mem (bvadd #x0000000000000007 init_RSI)) #x00)
(= (select mem init_RSI) ((_ extract 7 0) RDI))
(= (select mem (bvadd #x0000000000000001 init_RSI)) ((_ extract 15 8) RDI))
(= (select mem (bvadd #x0000000000000002 init_RSI)) ((_ extract 23 16) RDI))
(= (select mem (bvadd #x0000000000000003 init_RSI)) ((_ extract 31 24) RDI))
(= (select mem (bvadd #x0000000000000004 init_RSI)) ((_ extract 39 32) RDI))
(= (select mem (bvadd #x0000000000000005 init_RSI)) ((_ extract 47 40) RDI))
(= (select mem (bvadd #x0000000000000006 init_RSI)) ((_ extract 55 48) RDI))
(= (select mem (bvadd #x0000000000000007 init_RSI)) ((_ extract 63 56) RDI))
))" \
    -- ./main
}

run
