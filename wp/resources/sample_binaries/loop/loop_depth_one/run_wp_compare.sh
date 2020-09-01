# test that an unrolled loop does not effect results in the comparative case

# Should return UNSAT 

run() {
  bap wp \
    --func=foo \
    --num-unroll=3 \
    --postcond="(assert (= RAX_orig RAX_mod))" \
    --no-byteweight \
    -- main_1 main_2
}

run
