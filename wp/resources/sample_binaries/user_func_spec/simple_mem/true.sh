# Says that
# mem at (RSI + 0) equals 3
# mem at (RSI + 0) equals RDI
# RAX = 3

# wp should infer the bottom 8 bits of RAX are #x03,
#  since we call (mov rax, rdi) right after subroutine is called in main  

run () {
  bap wp \
      --func=main \
      --show="precond-internal,colorful"\
      --postcond="(assert (= ((_ extract 7 0) RAX) #x03))" \
    --user-func-spec="subroutine, (assert true), (assert (and
(= (select mem init_RSI) #x03)
(= (select mem init_RSI) ((_ extract 7 0) RDI) ) 
))" \
    -- ./main
}


run
