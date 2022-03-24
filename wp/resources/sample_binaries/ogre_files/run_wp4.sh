# Check to see if the two versions of f1 return the same value.  They don't.
# uses two different ogre files to find the two f1s in the two stripped
# binaries.
#
# Should be SAT

run () {
    bap wp \
      --func=f1 \
      --ogre-orig=main1.ogre \
      --ogre-mod=main2.ogre \
      --postcond="(assert (= R0_orig R0_mod))" \
      -- ./bin/main_1_stripped ./bin/main_2_stripped
}

run
