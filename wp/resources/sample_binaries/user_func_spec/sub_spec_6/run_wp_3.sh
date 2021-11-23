# Should return SAT.

# This is run_wp_1 but with an off-by-one error in the orig g spec, to show we
# get SATs when our specs don't provide the needed information.

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --user-func-specs-orig="g,(assert true),(assert (= RAX (bvadd init_RDI (_ bv7 64))))" \
    --user-func-specs-mod="g,(assert true),(assert (= RAX (bvadd init_RDI (_ bv4 64))))" \
    -- ./bin/orig ./bin/mod
}

run

