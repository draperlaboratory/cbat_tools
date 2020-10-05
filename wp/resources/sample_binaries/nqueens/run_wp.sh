# A program which trips an assert when the bit encoding
# of the nqueens problem is solved for n=$1.

# Should return SAT

run_net () {
  bap wp \
    --func=encode_nqueens \
    --trip-asserts \
    --num-unroll=0 \
    --inline="sub*" \
    -- bin/main_$1
}

run_net $1

