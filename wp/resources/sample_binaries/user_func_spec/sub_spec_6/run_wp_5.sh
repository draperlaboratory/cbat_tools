#!/bin/sh

# Should return UNSAT.

# This is similar to run_wp_1, except we verify the exact return values of both
# functions, rather than just a relative spec.

# In orig, `g` is called with 6 as an argument, while in mod it is called with
# `10`.  We give `g` two different function summaries, adding 4 in the orig case
# and 8 in the other, so we can prove that the result works out the same.

run () {
  bap wp \
    --func=main \
    --postcond="(assert (and (= RAX_orig (_ bv14 64)) (= RAX_mod (_ bv14 64))))"  \
    --user-func-specs-orig="g,(assert true),(assert (= RAX (bvadd init_RDI (_ bv8 64))))" \
    --user-func-specs-mod="g,(assert true),(assert (= RAX (bvadd init_RDI (_ bv4 64))))" \
    -- ./bin/orig ./bin/mod
}

run

