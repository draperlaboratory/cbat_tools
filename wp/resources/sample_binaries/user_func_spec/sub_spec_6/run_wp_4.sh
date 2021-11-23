# Should return SAT.

# This is run_wp_2 but with an off-by-one error in the mod g spec, to show we
# get SATs when our specs don't provided the needed information.

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --user-func-specs-orig="g,(assert true),
(declare-fun g_spec ((_ BitVec 64)) (_ BitVec 64))
(assert (= RAX (g_spec init_RDI)))" \
    --user-func-specs-mod="g,(assert true),
(declare-fun g_spec ((_ BitVec 64)) (_ BitVec 64))
(assert (= RAX (g_spec (bvsub init_RDI (_ bv3 64)))))" \
    -- ./bin/orig ./bin/mod
}

run
