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
      --postcond="(assert (= RAX #x0000000000000003))" \
    --user-func-spec="greg_memcpy, (assert true), (assert (and
(= init_RSI #x0000000000000003) (= RDI init_RSI)))" \
    -- ./main
}


run

greg_memcpy:
	mov rsi, rdi

main:
	call greg_memcpy
	mov rax, rdi
	ret

