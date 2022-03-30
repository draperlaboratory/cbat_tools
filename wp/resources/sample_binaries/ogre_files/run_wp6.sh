# Checks to see if f1 in main_2 returns 1 more than f1 in main_1.  It should.
# We use unstripped main_1 and stripped main_2 and only provide ogre for
# the latter.
#
# Should be UNSAT

run () {
    bap wp \
      --func=f1 \
      --ogre-mod=main2.ogre \
      --postcond="(assert (= (bvadd (_ bv1 32) R0_orig) R0_mod))" \
      -- ./bin/main_1 ./bin/main_2_stripped
}

run
