# Should return SAT: Since when RAX is 0x67, RDI will then trigger the assert(0)
#(= (select mem (bvadd xvar16 RDI)) (select mem (bvadd xvar16 RSI)))

run () {
  bap wp \
    --func=main \
    --postcond="(assert true)" \
    ./bin/main
}


run
