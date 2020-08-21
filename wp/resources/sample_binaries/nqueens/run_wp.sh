# A program which trips an assert when the bit encoding
# of the nqueens problem is solved for n=4.

# Should return SAT

set -x

run () {
  bap wp \
    --func=encode_nqueens \
    --trip-asserts \
    --show=precond-smtlib \
    --num-unroll=0 \
    -- main
}

run
