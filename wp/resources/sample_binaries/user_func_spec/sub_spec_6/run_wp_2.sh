# Should return UNSAT.

# In orig, `g` is called with 6 as an argument, while in mod it is called with
# `10`.

# Here again we give `g` two different summaries to account for this difference,
# but this time we do it a different way: by using an uninterpreted function to
# model the behavior of the original g, and then say that the modified g is like
# calling that function _with a different argument_ (in particular, we say
# mod_g(x) = orig_g(x-4))

# Note that we must declare the uninterpreted function in both specs, so that
# they parse, but Z3 will treat this as one symbol.

run () {
  bap wp \
    --func=main \
    --compare-post-reg-values=RAX \
    --user-func-specs-orig="g,(assert true),
(declare-fun g_spec ((_ BitVec 64)) (_ BitVec 64))
(assert (= RAX (g_spec init_RDI)))" \
    --user-func-specs-mod="g,(assert true),
(declare-fun g_spec ((_ BitVec 64)) (_ BitVec 64))
(assert (= RAX (g_spec (bvsub init_RDI (_ bv4 64)))))" \
    -- ./bin/orig ./bin/mod
}

run
