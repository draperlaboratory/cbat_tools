# Should return SAT.

# Here we're checking the exact results of both main functions, but we're using
# the relative specification from run_wp_2, so we should get SAT.  That spec is
# enough to prove that the orig and mod versions of main return the same thing,
# but not exactly what value that is.

run () {
  bap wp \
    --func=main \
    --postcond="(assert (and (= RAX_orig (_ bv14 64)) (= RAX_mod (_ bv14 64))))"  \
    --user-func-specs-orig="g,(assert true),
(declare-fun g_spec ((_ BitVec 64)) (_ BitVec 64))
(assert (= RAX (g_spec init_RDI)))" \
    --user-func-specs-mod="g,(assert true),
(declare-fun g_spec ((_ BitVec 64)) (_ BitVec 64))
(assert (= RAX (g_spec (bvsub init_RDI (_ bv4 64)))))" \
    -- ./bin/orig ./bin/mod
}

run

