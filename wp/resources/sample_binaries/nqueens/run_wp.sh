# A program which trips an assert when the bit encoding
# of the nqueens problem is solved for n=4.

# Should return SAT

run_split () {
  bap wp \
    --func=encode_nqueens_split \
    --trip-asserts \
    --num-unroll=0 \
    --debug=constraint-stats,eval-constraint-stats,z3-solver-stats \
    -- bin/main_$1
}

run_split_2 () {
  bap wp \
    --func=encode_nqueens_2_split \
    --trip-asserts \
    --num-unroll=0 \
    --debug=constraint-stats,eval-constraint-stats,z3-solver-stats \
    -- bin/main_$1
}

run_net () {
  bap wp \
    --func=encode_nqueens_net \
    --trip-asserts \
    --num-unroll=0 \
    --inline="sub*" \
    -- bin/main_$1
}

run_net $1

