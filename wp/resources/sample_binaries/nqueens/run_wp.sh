# A program which trips an assert when the bit encoding 
# of the nqueens problem is solved for n=4.
 
# Should return SAT

set -x

compile () {
  make
}

run () {
  bap main --pass=wp \
    --wp-function=encode_nqueens \
    --wp-trip-assert \
    --wp-show=precond-smtlib \
    --wp-num-unroll=0
}

compile && run
