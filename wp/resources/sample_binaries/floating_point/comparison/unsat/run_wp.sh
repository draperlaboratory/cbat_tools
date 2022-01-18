# A test that compares two binaries that perform an addition operation on the
# same two floating point numbers.

# Should return UNSAT

run () {
  bap wp \
    --func=foo \
    --show=bir,precond-internal,refuted-goals \
    --init-mem \
    --compare-post-reg-values=YMM0 \
    --bil-enable-intrinsic=:unknown \
    -- ./bin/main_1 ./bin/main_2
}

run
